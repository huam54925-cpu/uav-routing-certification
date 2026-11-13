"""Paired comparator experiment, with independent phase/coordinate-count checks.

Requires the built Lean comparison benchmark module. Records and generated
summaries stay under verification/runs; no compared state pairs are serialized.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import queue
import statistics
import subprocess
import threading
import time

from run_tree_budget_subtree_stats import Reference, FIELDS, enumerate_matrices

DETAIL = """calls keyVectorCalls keyRejects costVectorCalls costRejects equalStates
keyCoordinateChecks ratCoordinateChecks""".split()
ARMS = ["C_original", "F_original", "C_K", "C_B", "F_K", "F_B"]


def scan(xs, ys):
    count = 0
    for x, y in zip(xs, ys):
        count += 1
        if x != y:
            return False, count
    return True, count


def detailed(x, y, cost_first):
    out = dict.fromkeys(DETAIL, 0)
    out["calls"] = 1
    for field in ([1, 0] if cost_first else [0, 1]):
        ok, count = scan(x[field], y[field])
        out["costVectorCalls" if field else "keyVectorCalls"] += 1
        out["ratCoordinateChecks" if field else "keyCoordinateChecks"] += count
        if not ok:
            out["costRejects" if field else "keyRejects"] += 1
            return False, out
    out["equalStates"] = 1
    return True, out


class PhaseReference(Reference):
    """Explicit loops, event increments, no use of Lean's profile recurrences."""

    def __init__(self, record, full, native, cost_first):
        super().__init__(record, full=full)
        self.native, self.cost_first = native, cost_first
        self.rows = []
        self.stage = None

    def dedup(self, values):
        node, stage, position = self.stage
        out = []
        counts = dict.fromkeys(DETAIL, 0)
        for x in reversed(values):
            found = False
            for y in out:
                self.bump("eqCalls")
                if stage == "node" and not self.native:
                    found, ds = detailed(x, y, self.cost_first)
                else:
                    found = x == y
                    ds = dict.fromkeys(DETAIL, 0)
                    ds["calls"] = 1
                for k in DETAIL:
                    counts[k] += ds[k]
                if found:
                    break
            if not found:
                out.insert(0, x)
        self.bump("dedupInput", len(values))
        self.bump("dedupOutput", len(out))
        self.peak(len(values), len(out))
        self.rows.append({"node": node, "stage": stage, "position": position,
                          "input": len(values), "output": len(out),
                          "counts": [counts[k] for k in DETAIL],
                          "detailAvailable": stage == "node" and not self.native})
        return out

    def node(self, v):
        self.bump("nodeCalls")
        tables = [self.node(u) for u in self.children(v)]
        qs = self.compositions(self.m, self.h[v])
        self.bump("columnsGenerated", len(qs))
        if self.parent[v] == self.root:
            qs = [q for q in qs if all(n <= 1 for n in q)]
        self.bump("columnsAccepted", len(qs))
        weight = self.s[v] + (0 if self.parent[v] == self.root else self.s[self.parent[v]])
        raw_node = []
        for q in qs:
            active = tuple(n > 0 for n in q)
            base = []
            for n in q:
                self.bump("ratMuls")
                base.append(weight * n)
            current = [tuple(base)]
            self.peak(1, 1)
            for pos in reversed(range(len(tables))):
                allowed = []
                for e in tables[pos]:
                    self.bump("subsetCalls")
                    if all(not a or b for a, b in zip(self.active(e), active)):
                        allowed.append(e)
                raw = []
                for e in allowed:
                    for b in current:
                        self.bump("insidePairs")
                        raw.append(self.add(e[1], b))
                self.stage = v, "inside", pos
                current = self.dedup(raw)
            raw_node.extend((q if self.full else active, b) for b in current)
        self.stage = v, "node", 0
        result = self.dedup(raw_node)
        self.tables[v] = result
        return result

    def run(self):
        tables = [self.node(u) for u in self.children(self.root)]
        current = [((0,) * self.m, (0,) * self.m)]
        self.peak(1, 1)
        for pos in reversed(range(len(tables))):
            raw = []
            pairs = 0
            for e in tables[pos]:
                for used, cost in current:
                    pairs += 1
                    self.bump("rootPairs")
                    next_used = tuple(a + int(b) for a, b in zip(used, self.active(e)))
                    next_cost = self.add(cost, e[1])
                    if any(n > 1 for n in next_used):
                        self.bump("rootRejected")
                    else:
                        raw.append((next_used, next_cost))
            self.peak(pairs, 0)
            self.stage = self.root, "root", pos
            current = self.dedup(raw)
        for used, cost in current:
            self.bump("acceptCalls")
            if all(n == 1 and c <= self.budget for n, c in zip(used, cost)):
                return True
        return False


def verify(records):
    inputs = {r["case"]: r for r in records if r.get("kind") == "input"}
    done = {r["case"] for r in records if r.get("phase") == "case_done"}
    for name in done:
        source = inputs[name]
        assert enumerate_matrices(source) == source["answer"], (name, "matrix decision")
        ds = [r for r in records if r.get("kind") == "diagnostic" and r["case"] == name]
        assert {(r["representation"], r["strategy"]) for r in ds} == {
            (rep, st) for rep in ["compact", "full"] for st in ["native", "key", "cost"]}
        for r in ds:
            full = r["representation"] == "full"
            ref = PhaseReference(source, full, r["strategy"] == "native", r["strategy"] == "cost")
            assert ref.run() == r["answer"] == source["answer"]
            assert ref.count == dict(zip(FIELDS, r["stats"])), (name, "17 metrics", r["strategy"])
            assert ref.rows == r["rows"], (name, r["representation"], r["strategy"], "phase/scan counts")
            assert sum(x["counts"][0] for x in r["rows"]) == ref.count["eqCalls"]
            base = Reference(source, full=full)
            base.run()
            assert base.tables == ref.tables and base.count == ref.count, (name, "ordered baseline collapse")
            for v, table in ref.tables.items():
                expected = enumerate_matrices(source, v)[int(full)]
                assert set(table) == expected, (name, v, "local matrices")
        samples = [r for r in records if r.get("kind") == "timing" and r["case"] == name]
        by_arm = [{r["round"] for r in samples if r["arm"] == a} for a in range(6)]
        assert by_arm[0] and all(x == by_arm[0] for x in by_arm)
        assert len(samples) == 6 * len(by_arm[0]), (name, "duplicate or missing samples")
        assert len({r["reps"] for r in samples}) == 1, (name, "unmatched batch sizes")
        assert all(r["checksum"] == int(source["answer"]) * r["reps"] for r in samples)
    return len(done)


def summarize(records):
    done = [r["case"] for r in records if r.get("phase") == "case_done"]
    output = []
    for name in done:
        samples = [r for r in records if r.get("kind") == "timing" and r["case"] == name]
        rounds = sorted({r["round"] for r in samples})
        times = {(r["arm"], r["round"]): r["ns"] / r["reps"] for r in samples}
        ds = [r for r in records if r.get("kind") == "diagnostic" and r["case"] == name]
        row = {"case": name, "reps": samples[0]["reps"], "diagnostics": {},
               "medians_ns": {ARMS[a]: statistics.median(times[a, j] for j in rounds) for a in range(6)}}
        ratios = {}
        for label, a, b in [("C_original/F_original", 0, 1), ("C_K/F_K", 2, 4),
                            ("C_K/C_B", 2, 3), ("F_B/F_K", 5, 4),
                            ("C_K/C_original", 2, 0), ("F_K/F_original", 4, 1)]:
            pairs = [times[a, j] / times[b, j] for j in rounds]
            ratios[label] = {"per_round": pairs, "median_paired": statistics.median(pairs),
                             "ratio_of_medians": row["medians_ns"][ARMS[a]] / row["medians_ns"][ARMS[b]]}
        row["ratios"] = ratios
        for r in ds:
            stages = {}
            for event in r["rows"]:
                acc = stages.setdefault(event["stage"], dict.fromkeys(DETAIL + ["input", "output"], 0))
                acc["input"] += event["input"]
                acc["output"] += event["output"]
                for k, value in zip(DETAIL, event["counts"]):
                    acc[k] += value
            row["diagnostics"][r["representation"] + "_" + r["strategy"]] = stages
        output.append(row)
    return output


def supervise(args, root, out):
    records, outcomes = [], []
    start, attempt = 0, 0
    while True:
        cmd = ["lake", "env", "lean", "--run", "verification/RunTreeBudgetSubtreeCompare.lean",
               str(args.rounds), str(args.target_ms), str(start)]
        p = subprocess.Popen(cmd, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, encoding="utf-8", errors="replace")
        q = queue.Queue()

        def read():
            for line in p.stdout:
                q.put(line)
            q.put(None)

        threading.Thread(target=read, daemon=True).start()
        deadline, case_deadline = time.monotonic() + 600, float("inf")
        current, idx, phase, timeout = None, start, "startup", False
        with (out / f"attempt-{attempt}.jsonl").open("w", encoding="utf-8") as log:
            while True:
                try:
                    line = q.get(timeout=max(.001, min(deadline, case_deadline) - time.monotonic()))
                except queue.Empty:
                    timeout = True
                    if os.name == "nt":
                        subprocess.run(["taskkill", "/PID", str(p.pid), "/T", "/F"],
                                       capture_output=True, check=False)
                    else:
                        p.kill()
                    p.wait()
                    outcomes.append({"case": current, "index": idx, "status": "timeout", "phase": phase})
                    break
                if line is None:
                    p.wait()
                    if p.returncode:
                        raise RuntimeError(f"Lean exited {p.returncode}; see {log.name}")
                    break
                log.write(line)
                log.flush()
                try:
                    r = json.loads(line)
                except json.JSONDecodeError:
                    continue
                records.append(r)
                if "phase" in r:
                    phase = r["phase"]
                    deadline = time.monotonic() + args.phase_seconds
                if r.get("phase") == "case_start":
                    current, idx = r["case"], r["index"]
                    case_deadline = time.monotonic() + args.case_seconds
                if r.get("phase") == "case_done":
                    outcomes.append({"case": current, "index": idx, "status": "completed"})
                    print(f"completed {idx}: {current}", flush=True)
        (out / "records.json").write_text(json.dumps(records, indent=2), encoding="utf-8")
        (out / "outcomes.json").write_text(json.dumps(outcomes, indent=2), encoding="utf-8")
        if not timeout:
            break
        if current is None:
            raise RuntimeError("startup timeout")
        print(f"timeout {current} in {phase}; not an infeasibility result", flush=True)
        start, attempt = idx + 1, attempt + 1
    return records, outcomes


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rounds", type=int, default=7)
    ap.add_argument("--target-ms", type=int, default=100)
    ap.add_argument("--phase-seconds", type=float, default=60)
    ap.add_argument("--case-seconds", type=float, default=300)
    ap.add_argument("--output", default="verification/runs/issue19-compare-20261113/benchmark")
    ap.add_argument("--verify-only", action="store_true")
    args = ap.parse_args()
    if args.rounds < 1 or args.target_ms < 1:
        ap.error("positive rounds and target-ms required")
    root = Path(__file__).resolve().parents[1]
    out = (root / args.output).resolve()
    if not out.is_relative_to((root / "verification/runs").resolve()):
        ap.error("output must stay under verification/runs")
    out.mkdir(parents=True, exist_ok=True)
    if args.verify_only:
        records = json.loads((out / "records.json").read_text(encoding="utf-8"))
        outcomes = json.loads((out / "outcomes.json").read_text(encoding="utf-8"))
    else:
        env = {"platform": platform.platform(), "cpu": platform.processor(),
               "logical_cpus": os.cpu_count(), "rounds": args.rounds,
               "target_ms": args.target_ms, "batch_cap": 4096, "warmup_per_arm": 1,
               "phase_seconds": args.phase_seconds, "case_seconds": args.case_seconds,
               "runtime": "Lean --run / compiled imports", "arms": ARMS}
        (out / "environment.json").write_text(json.dumps(env, indent=2), encoding="utf-8")
        records, outcomes = supervise(args, root, out)
    n = verify(records)
    (out / "summary.json").write_text(json.dumps(summarize(records), indent=2), encoding="utf-8")
    print(f"PASS: {n} cases; all phase rows and detailed counts, 17-metric collapse, ordered tables, matrices")
    print(f"Timeouts: {sum(r['status']=='timeout' for r in outcomes)}")


if __name__ == "__main__":
    main()
