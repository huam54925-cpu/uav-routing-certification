"""Supervise compiled Lean DP experiments and independently check their records.

Build LeanCompletion.UAV.TreeBudgetSubtreeStatsBench first. The tiny --run driver
imports that compiled module; elaboration/startup is outside internal timers.
Raw records and generated summaries must remain under verification/runs/.
"""
import argparse
from fractions import Fraction as Q
from itertools import product
import json
import os
from pathlib import Path
import platform
import queue
import statistics
import subprocess
import threading
import time

FIELDS = """nodeCalls compositionCalls rangeChoices columnsGenerated columnsAccepted
subsetCalls insidePairs rootPairs rootRejected ratAdds ratMuls dedupInput dedupOutput
eqCalls acceptCalls maxRawTable maxDedupTable""".split()


class Reference:
    """Independent event-counting implementation, with explicit nested loops.

    Unlike the Lean profile formulas, arithmetic and pair counters are incremented
    at each operation. No set/hash operation implements the measured dedup.
    """

    def __init__(self, record, full=False, fast=False):
        self.r = record
        self.full, self.fast = full, fast
        self.m, self.root = record["m"], record["root"]
        self.h, self.parent = record["H"], record["parent"]
        self.s, self.budget = list(map(Q, record["s"])), Q(record["T"])
        self.count = dict.fromkeys(FIELDS, 0)
        self.tables = {}

    def bump(self, field, amount=1):
        self.count[field] += amount

    def peak(self, raw, kept):
        self.count["maxRawTable"] = max(self.count["maxRawTable"], raw)
        self.count["maxDedupTable"] = max(self.count["maxDedupTable"], kept)

    def children(self, v):
        return [u for u, p in enumerate(self.parent) if u != self.root and p == v]

    def compositions(self, m, h):
        self.bump("compositionCalls")
        if self.fast and self.m == 1:
            return [(h,)]
        if m == 0:
            return [()] if h == 0 else []
        result = []
        for head in range(h + 1):
            self.bump("rangeChoices")
            for tail in self.compositions(m - 1, h - head):
                result.append((head,) + tail)
        return result

    def dedup(self, values):
        out = []
        for x in reversed(values):
            found = False
            for y in out:
                self.bump("eqCalls")
                if x == y:
                    found = True
                    break
            if not found:
                out.insert(0, x)
        self.bump("dedupInput", len(values))
        self.bump("dedupOutput", len(out))
        self.peak(len(values), len(out))
        return out

    def add(self, x, y):
        out = []
        for a, b in zip(x, y):
            self.bump("ratAdds")
            out.append(a + b)
        return tuple(out)

    def active(self, state):
        return tuple(q > 0 for q in state[0]) if self.full else state[0]

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
            for table in reversed(tables):
                allowed = []
                for e in table:
                    self.bump("subsetCalls")
                    if all(not a or b for a, b in zip(self.active(e), active)):
                        allowed.append(e)
                raw = []
                for e in allowed:
                    for b in current:
                        self.bump("insidePairs")
                        raw.append(self.add(e[1], b))
                current = self.dedup(raw)
            raw_node.extend((q if self.full else active, b) for b in current)
        result = self.dedup(raw_node)
        self.tables[v] = result
        return result

    def run(self):
        tables = [self.node(u) for u in self.children(self.root)]
        current = [((0,) * self.m, (Q(0),) * self.m)]
        self.peak(1, 1)
        for table in reversed(tables):
            raw = []
            pairs = 0
            for e in table:
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
            current = self.dedup(raw)
        for used, cost in current:
            self.bump("acceptCalls")
            if all(n == 1 and c <= self.budget for n, c in zip(used, cost)):
                return True
        return False


def columns(m, total):
    """Mathematical enumeration, independent of the counted recursive algorithm."""
    if m == 0:
        return [()] if total == 0 else []
    if m == 1:
        return [(total,)]
    return [(n,) + q for n in range(total + 1) for q in columns(m - 1, total - n)]


def enumerate_matrices(record, top=None):
    """Independent matrices: column sums, ancestor closure, root degree, row cost.

    For a subtree returns both full and compact sets using direct row-degree
    service cost and the parent charge, not the DP's linear-weight recurrence.
    """
    ref = Reference(record)
    vertices = []

    def descend(v):
        vertices.append(v)
        for u in ref.children(v):
            descend(u)

    if top is None:
        for u in ref.children(ref.root):
            descend(u)
    else:
        descend(top)
    options = []
    for v in vertices:
        qs = columns(ref.m, ref.h[v])
        if ref.parent[v] == ref.root:
            qs = [q for q in qs if all(n <= 1 for n in q)]
        options.append(qs)
    compact, full = set(), set()
    feasible = False
    for chosen in product(*options):
        matrix = dict(zip(vertices, chosen))
        if any(matrix[v][i] > 0 and matrix[ref.parent[v]][i] == 0
               for v in vertices if ref.parent[v] in matrix for i in range(ref.m)):
            continue
        costs = tuple(sum(ref.s[v] * (matrix[v][i] + sum(matrix[u][i] for u in ref.children(v)))
                          for v in vertices) for i in range(ref.m))
        if top is None:
            degree = tuple(sum(matrix[u][i] for u in ref.children(ref.root)) for i in range(ref.m))
            if all(n == 1 and c <= ref.budget for n, c in zip(degree, costs)):
                feasible = True
        else:
            charge = 0 if ref.parent[top] == ref.root else ref.s[ref.parent[top]]
            linear = tuple(c + charge * n for c, n in zip(costs, matrix[top]))
            full.add((matrix[top], linear))
            compact.add((tuple(n > 0 for n in matrix[top]), linear))
    return feasible if top is None else (compact, full)


def verify(records):
    cases = {r["case"]: r for r in records if r.get("phase") == "counts"}
    tables = {(r["case"], r["node"]): r for r in records if "compactTable" in r}
    complete = {r["case"] for r in records if r.get("phase") == "case_done"}
    assert complete <= cases.keys(), "completed case lacks count record"
    for name, record in cases.items():
        if name not in complete:
            continue
        assert enumerate_matrices(record) == record["answer"], (name, "matrix answer")
        for mode in ["compact", "full", "fast"]:
            ref = Reference(record, full=mode == "full", fast=mode == "fast")
            assert ref.run() == record["answer"], (name, mode, "answer")
            expected = dict(zip(FIELDS, record[mode]))
            assert ref.count == expected, (name, mode, {
                k: (ref.count[k], expected[k]) for k in FIELDS if ref.count[k] != expected[k]})
            for v, table in ref.tables.items():
                key = "fullTable" if mode == "full" else "compactTable"
                actual = [(tuple(a), tuple(map(Q, b))) for a, b in tables[name, v][key]]
                assert table == actual, (name, mode, v, "table order")
        for v in range(len(record["parent"])):
            if v == record["root"]:
                continue
            c, f = enumerate_matrices(record, v)
            for key, expected in [("compactTable", c), ("fullTable", f)]:
                actual = {(tuple(a), tuple(map(Q, b))) for a, b in tables[name, v][key]}
                assert actual == expected, (name, v, key, "independent local matrices")
        for r in records:
            if r.get("case") == name and "checksum" in r:
                assert r["checksum"] == r["reps"] * int(record["answer"]), (name, "timed answer")
        rounds = [{r["round"] for r in records if r.get("case") == name and
                   "ns" in r and r["mode"] == mode} for mode in range(3)]
        assert rounds[0] and rounds[0] == rounds[1] == rounds[2], (name, "unbalanced rounds")
    return len(complete)


def summarize(records):
    output = []
    complete = {r["case"] for r in records if r.get("phase") == "case_done"}
    for r in records:
        if r.get("phase") != "counts":
            continue
        done = r["case"] in complete
        row = {"case": r["case"], "answer": r["answer"],
               "status": "completed" if done else "incomplete"}
        for mode, idx in [("compact", 0), ("full", 1), ("fast", 2)]:
            ns = [x["ns"] / x["reps"] for x in records
                  if x.get("case") == r["case"] and "ns" in x and x["mode"] == idx]
            row[mode] = {"counts": dict(zip(FIELDS, r[mode])), "samples_ns_per_call": ns,
                         "median_ns_per_call": statistics.median(ns) if ns and done else None}
        output.append(row)
    return output


def run(args, root, out):
    records = []
    outcomes = []
    start = 0
    attempt = 0
    while True:
        command = ["lake", "env", "lean", "--run", "verification/RunTreeBudgetSubtreeStats.lean",
                   str(args.reps), str(args.rounds), str(start)]
        p = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, encoding="utf-8", errors="replace")
        messages = queue.Queue()

        def read():
            for line in p.stdout:
                messages.put(line)
            messages.put(None)

        threading.Thread(target=read, daemon=True).start()
        deadline = time.monotonic() + args.startup_seconds
        case_deadline = float("inf")
        current, index, phase = None, start, "startup"
        timeout = False
        with (out / f"attempt-{attempt}.jsonl").open("w", encoding="utf-8") as log:
            while True:
                try:
                    line = messages.get(timeout=max(.001, min(deadline, case_deadline) - time.monotonic()))
                except queue.Empty:
                    timeout = True
                    if os.name == "nt":
                        subprocess.run(["taskkill", "/PID", str(p.pid), "/T", "/F"],
                                       capture_output=True, check=False)
                    else:
                        p.kill()
                    p.wait()
                    outcomes.append({"case": current, "index": index, "status": "timeout",
                                     "phase": phase})
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
                if phase == "case_start" and "index" in r:
                    current, index = r["case"], r["index"]
                    case_deadline = time.monotonic() + args.case_seconds
                if r.get("phase") == "case_done":
                    outcomes.append({"case": r["case"], "index": r["index"], "status": "completed"})
                    print(f"completed {r['index']}: {r['case']}", flush=True)
        (out / "records.json").write_text(json.dumps(records, indent=2), encoding="utf-8")
        (out / "outcomes.json").write_text(json.dumps(outcomes, indent=2), encoding="utf-8")
        if not timeout:
            break
        if current is None:
            raise RuntimeError("startup timeout; no case result")
        print(f"timeout {index}: {current} ({phase}); continuing at next case", flush=True)
        start, attempt = index + 1, attempt + 1
    return records, outcomes


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--reps", type=int, default=20)
    ap.add_argument("--rounds", type=int, default=7)
    ap.add_argument("--phase-seconds", type=float, default=30)
    ap.add_argument("--case-seconds", type=float, default=180)
    ap.add_argument("--startup-seconds", type=float, default=600)
    ap.add_argument("--output", default="verification/runs/issue19-stats-20261113/benchmark")
    ap.add_argument("--verify-only", action="store_true")
    args = ap.parse_args()
    if args.reps < 1 or args.rounds < 1:
        ap.error("positive reps and rounds required")
    root = Path(__file__).resolve().parents[1]
    out = (root / args.output).resolve()
    if not out.is_relative_to((root / "verification/runs").resolve()):
        ap.error("output must stay under verification/runs")
    out.mkdir(parents=True, exist_ok=True)
    if args.verify_only:
        records = json.loads((out / "records.json").read_text(encoding="utf-8"))
        outcomes = json.loads((out / "outcomes.json").read_text(encoding="utf-8"))
    else:
        metadata = {"platform": platform.platform(), "cpu": platform.processor(),
                    "logical_cpus": os.cpu_count(), "python": platform.python_version(),
                    "reps": args.reps, "rounds": args.rounds, "warmup_per_mode": 1,
                    "phase_seconds": args.phase_seconds, "case_seconds": args.case_seconds,
                    "runtime": "Lean --run / compiled imports",
                    "timing": "IO.monoNanosNow; whole uninstrumented checker; cyclic mode order"}
        (out / "environment.json").write_text(json.dumps(metadata, indent=2), encoding="utf-8")
        records, outcomes = run(args, root, out)
    completed = verify(records)
    report = summarize(records)
    (out / "summary.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"PASS: {completed} cases; ordered tables, all 17 counters in 3 modes, and independent matrices")
    timeouts = sum(x["status"] == "timeout" for x in outcomes)
    print(f"Timeouts: {timeouts} (not interpreted as infeasible)")


if __name__ == "__main__":
    main()
