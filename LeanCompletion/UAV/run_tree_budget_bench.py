"""Supervise tiny Lean experiments; keep raw output under verification/runs.

From the repository root:
  py -3 LeanCompletion/UAV/run_tree_budget_bench.py --reps 21
The source is reproducibility tooling, not a generated run artifact.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import queue
import subprocess
import threading
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--reps", type=int, default=21)
    ap.add_argument("--phase-seconds", type=float, default=5)
    ap.add_argument("--startup-seconds", type=float, default=600)
    ap.add_argument("--cases", nargs="+", default=["all"])
    ap.add_argument("--output", default="verification/runs/memo-performance-20261104/measured")
    args = ap.parse_args()
    if not 1 <= args.reps <= 100:
        ap.error("reps must be between 1 and 100")
    root = Path(__file__).resolve().parents[2]
    out = (root / args.output).resolve()
    allowed = (root / "verification/runs").resolve()
    if not out.is_relative_to(allowed):
        ap.error("output must be under verification/runs")
    out.mkdir(parents=True, exist_ok=True)
    env = {"platform": platform.platform(), "python": platform.python_version(),
           "cpu": platform.processor(), "logical_cpus": os.cpu_count(),
           "reps": args.reps, "warmup": 1, "phase_seconds": args.phase_seconds,
           "startup_seconds": args.startup_seconds,
           "entry": "lake env lean --run LeanCompletion/UAV/TreeBudgetBench.lean"}
    (out / "environment.json").write_text(json.dumps(env, indent=2), encoding="utf-8")
    summary = []
    for case in args.cases:
        cmd = ["lake", "env", "lean", "--run", "LeanCompletion/UAV/TreeBudgetBench.lean",
               case, str(args.reps)]
        started = time.monotonic()
        p = subprocess.Popen(cmd, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, encoding="utf-8", errors="replace")
        q = queue.Queue()

        def read_lines():
            for line in p.stdout:
                q.put(line)
            q.put(None)

        threading.Thread(target=read_lines, daemon=True).start()
        deadline = started + args.startup_seconds
        phase = "startup"
        status = "completed"
        records = []
        with (out / f"{case}.jsonl").open("w", encoding="utf-8") as log:
            while True:
                try:
                    line = q.get(timeout=max(0.001, deadline - time.monotonic()))
                except queue.Empty:
                    status = "timeout_unfinished"
                    # Terminate only this child process tree; never interpret as infeasible.
                    if os.name == "nt":
                        subprocess.run(["taskkill", "/PID", str(p.pid), "/T", "/F"],
                                       capture_output=True, check=False)
                    else:
                        p.kill()
                    p.wait()
                    break
                if line is None:
                    p.wait()
                    if p.returncode:
                        status = "error_unfinished"
                    break
                log.write(line)
                log.flush()
                try:
                    record = json.loads(line)
                except json.JSONDecodeError:
                    continue
                records.append(record)
                if "phase" in record:
                    phase = record["phase"]
                    deadline = time.monotonic() + args.phase_seconds
        result = {"case": case, "status": status, "last_phase": phase,
                  "returncode": p.returncode, "wall_seconds": time.monotonic() - started,
                  "records": records}
        summary.append(result)
        print(json.dumps({k: v for k, v in result.items() if k != "records"}), flush=True)
        (out / "results.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    if any(r["status"] != "completed" for r in summary):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
