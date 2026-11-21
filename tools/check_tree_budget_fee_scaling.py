#!/usr/bin/env python3
"""Actual fee-scaling TM2 regression and explicit axiom audit.

Expected numeric answers use Fraction and the product of all raw denominators.
The independent encoder is shared with the earlier paired-parser corpus.
Generated cases and raw output remain under ignored verification/runs/.
"""
import argparse
from fractions import Fraction
from itertools import product
from math import prod
from pathlib import Path
import random
import re
import shutil
import subprocess
import tempfile

from check_tree_budget_paired_parser import word, nat, integer, instance, certificate


def corpus():
    cases = []

    def add(tag, nums, dens, budget, budget_den, root=0, rows=None, parents=None, demands=None):
        n = len(nums)
        parents = parents if parents is not None else [root] * n
        demands = demands if demands is not None else [0] * n
        m = sum(h for i, (p, h) in enumerate(zip(parents, demands)) if i != root and p == root)
        x = instance(m, root, parents, demands, nums, dens, budget, budget_den)
        y = certificate([] if rows is None else rows)
        common = budget_den * prod(dens)
        fees = [Fraction(a, b) * common for a, b in zip(nums, dens)]
        scaled_budget = Fraction(budget, budget_den) * common
        assert all(a.denominator == 1 for a in fees) and scaled_budget.denominator == 1
        cases.append((tag, word(x) + y, "1",
                      "".join(integer(a.numerator) for a in fees), integer(scaled_budget.numerator)))
        return x, y

    x, y = add("two_vertices", [-2, 0], [4, 3], -3, 6,
               rows=[(7, [3, 0]), (2, [3, 0])], demands=[7, 1])
    add("repeated_denominators", [-2, 0, 3], [2, 3, 2], -2, 4, root=2,
        rows=[(0, [0, 0, 0])], demands=[1, 1, 0])
    add("carry", [255, 257], [255, 1], 1, 1, demands=[0, 1])
    add("zero_count_retained", [0], [1], 0, 1, rows=[(0, [0])])
    add("root_empty", [0], [1], 0, 1)
    add("huge_root_and_counts", [-2**40, 0], [2**20, 3], -2**30, 2**16,
        demands=[2**80, 1], rows=[(2**80, [0, 1]), (0, [0, 0])])
    for a, b, at, bt in product([-2, 0, 3], [1, 2, 4], [-3, 0, 2], [1, 3]):
        add(f"singleton_{a}_{b}_{at}_{bt}", [a], [b], at, bt)
    rng = random.Random(20261121)
    for k in range(128):
        n = rng.randrange(1, 5)
        root = rng.randrange(n)
        nums = [rng.randrange(-16, 17) for _ in range(n)]
        dens = [rng.randrange(1, 9) for _ in range(n)]
        rows = [(rng.randrange(4), [rng.randrange(3) for _ in range(n)])
                for _ in range(rng.randrange(4))]
        demands = [rng.randrange(4) for _ in range(n)]
        add(f"random_{k}", nums, dens, rng.randrange(-16, 17), rng.randrange(1, 9),
            root=root, rows=rows, demands=demands)
    for length in range(7):
        for bs in product("01", repeat=length):
            cases.append(("outer_short", "".join(bs), "0", "-", "-"))
    for i in range(0, len(x), 3):
        cases.append((f"instance_cut_{i}", word(x[:i]) + y, "0", "-", "-"))
    for i in range(0, len(y), 3):
        cases.append((f"certificate_cut_{i}", word(x) + y[:i], "0", "-", "-"))
    bad = instance(0, 0, [0], [0], [0], [0], 0, 1)
    cases.append(("zero_denominator", word(bad) + certificate([]), "0", "-", "-"))
    cases.append(("second_record_cut", word(x) + nat(2) + nat(7) + nat(2) +
                  nat(3) + nat(0) + nat(0) + "1", "0", "-", "-"))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--no-build", action="store_true")
    args = parser.parse_args()
    repo = args.repo.resolve()
    lake = shutil.which("lake")
    if not lake:
        raise SystemExit("No Lake executable found on PATH.")
    runs = repo / "verification/runs/fee-scaling"
    runs.mkdir(parents=True, exist_ok=True)

    def execute(command, name):
        result = subprocess.run([lake, *command], cwd=repo, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        (runs / name).write_bytes(result.stdout)
        text = result.stdout.decode("utf-8", errors="replace")
        if result.returncode or "sorryAx" in text or "declaration uses 'sorry'" in text:
            raise SystemExit(f"Failed {name}; inspect {runs / name}")
        return text

    if not args.no_build:
        execute(["build", "+LeanCompletion.UAV.TreeBudgetFeeScalingTotal",
                 "+LeanCompletion.UAV.TreeBudgetFeeScalingExamples"], "build.log")
    cases = corpus()
    with tempfile.TemporaryDirectory(prefix="corpus-", dir=runs) as temp:
        path = Path(temp) / "cases.tsv"
        path.write_bytes("".join("\t".join(row) + "\n" for row in cases).encode("ascii"))
        text = execute(["env", "lean", "--run", "verification/RunTreeBudgetFeeScaling.lean",
                        str(path)], "lean-corpus.log")
    marker = f"fee scaler agrees with specification on {len(cases)} cases"
    if marker not in text:
        raise SystemExit("Missing corpus completion record.")
    print(marker, flush=True)
    audit = repo / "verification/AuditTreeBudgetFeeScaling.lean"
    text = execute(["env", "lean", str(audit)], "axioms.log")
    names = re.findall(r"^#print axioms (\S+)$", audit.read_text(encoding="utf-8"), re.M)
    if not names or len(names) != len(set(names)):
        raise SystemExit("Empty or duplicate audit declarations.")
    for name in names:
        pattern = r"'" + re.escape(name) + r"'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
        match = re.search(pattern, text)
        if not match:
            raise SystemExit("Missing audit for " + name)
        used = {a.strip() for a in (match.group(1) or "").split(",") if a.strip()}
        if used - {"propext", "Classical.choice", "Quot.sound"}:
            raise SystemExit("Unexpected axioms for " + name)
    print(f"Axiom audit: {len(names)} declarations passed.", flush=True)


if __name__ == "__main__":
    main()
