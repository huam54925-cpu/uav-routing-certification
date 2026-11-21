#!/usr/bin/env python3
"""Exercise the actual paired TM2 and audit all explicit new declarations.

Corpus generation uses an independent encoder. Unknown mutated inputs are
compared against the Lean reference parser; named cases have explicit answers.
Generated inputs and raw reports stay under ignored verification/runs/.
"""
import argparse
import itertools
from pathlib import Path
import random
import re
import shutil
import subprocess
import tempfile


def word(s):
    return "".join("1" + bit for bit in s) + "0"


def nat(n):
    return word(bin(n)[2:][::-1] if n else "")


def integer(n):
    return str(int(n < 0)) + nat(abs(n))


def sequence(xs, encode=nat):
    return nat(len(xs)) + "".join(map(encode, xs))


def instance(m, root, parents, demands, nums, dens, budget, budget_den):
    return (nat(m) + nat(len(parents)) + nat(root) + sequence(parents) +
            sequence(demands) + sequence(nums, integer) + sequence(dens) +
            integer(budget) + nat(budget_den))


def certificate(rows):
    return sequence(rows, lambda row: nat(row[0]) + sequence(row[1]))


def corpus():
    cases = []

    def add(tag, x, y, expected="-", semantic="-"):
        cases.append((tag, word(x) + y, str(expected), str(semantic)))

    root = instance(0, 0, [0], [0], [0], [1], 0, 1)
    empty = certificate([])
    zero = certificate([(0, [0])])
    two = instance(1, 0, [0, 0], [7, 1], [-2, 0], [4, 3], -3, 6)
    same_rows = certificate([(7, [3, 0]), (2, [3, 0])])
    add("root_empty", root, empty, 1, 1)
    add("root_zero_multiplicity", root, zero, 1, 0)
    add("same_rows_different_counts", two, same_rows, 1)
    add("dimension_is_not_route_count", two, certificate([(7, [3])]), 0)
    add("second_record_cut", two, nat(2) + nat(7) + sequence([3, 0]) + nat(0) + "1", 0)
    add("certificate_tail", root, empty + "0", 0)
    add("instance_tail", root + "0", empty, 0)
    add("empty_instance", "", empty, 0)
    add("empty_certificate", root, "", 0)
    add("bad_route_count", instance(1, 0, [0], [0], [0], [1], 0, 1), zero, 0)
    add("zero_denominator", instance(0, 0, [0], [0], [0], [0], 0, 1), zero, 0)
    add("large_root_coordinate", instance(0, 0, [0], [2**80], [0], [3], 0, 5), zero, 1, 0)
    add("large_record_count", root, nat(2**90) + "101", 0)
    add("large_multiplicity", root, certificate([(2**90, [0])]), 1, 0)
    add("nonzero_root", instance(2, 1, [1, 1, 0], [2, 2**80, 7], [-1, 2, 0],
                                  [2, 2, 3], -2, 6), certificate([(0, [1, 0, 0])]), 1)
    for length in range(11):
        for digits in itertools.product("01", repeat=length):
            cases.append(("outer_short", "".join(digits), "0", "-"))
    rng = random.Random(902144)
    for trial in range(16):
        n = rng.randrange(1, 5)
        parents = [0] + [rng.randrange(i) for i in range(1, n)]
        demands = [rng.randrange(5) for _ in range(n)]
        m = sum(demands[i] for i in range(1, n) if parents[i] == 0)
        nums = [rng.randrange(-5, 6) for _ in range(n)]
        dens = [rng.randrange(1, 7) for _ in range(n)]
        x = instance(m, 0, parents, demands, nums, dens, rng.randrange(-5, 6), rng.randrange(1, 7))
        rows = [(rng.randrange(8), [rng.randrange(5) for _ in range(n)])
                for _ in range(rng.randrange(4))]
        y = certificate(rows)
        add(f"valid_{trial}", x, y, 1)
        add(f"x_tail_{trial}", x + "1", y, 0)
        add(f"y_tail_{trial}", x, y + "0", 0)
        for j in range(0, len(x), max(1, len(x)//12)):
            add(f"x_cut_{trial}_{j}", x[:j], y, 0)
            add(f"x_flip_{trial}_{j}", x[:j] + str(1-int(x[j])) + x[j+1:], y)
        for j in range(0, len(y), max(1, len(y)//12)):
            add(f"y_cut_{trial}_{j}", x, y[:j], 0)
            add(f"y_flip_{trial}_{j}", x, y[:j] + str(1-int(y[j])) + y[j+1:])
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
    runs = repo / "verification/runs/paired-parser"
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
        execute(["build", "+LeanCompletion.UAV.TreeBudgetPairedParserTotal",
                 "+LeanCompletion.UAV.TreeBudgetPairedParserExamples"], "build.log")
    cases = corpus()
    with tempfile.TemporaryDirectory(prefix="corpus-", dir=runs) as temp:
        path = Path(temp) / "cases.tsv"
        path.write_bytes("".join("\t".join(row) + "\n" for row in cases).encode("ascii"))
        text = execute(["env", "lean", "--run", "verification/RunTreeBudgetPairedParser.lean",
                        str(path)], "lean-corpus.log")
    marker = f"paired parser agrees with specification on {len(cases)} cases"
    if marker not in text:
        raise SystemExit("Missing paired corpus completion record.")
    print(marker, flush=True)
    audit = repo / "verification/AuditTreeBudgetPairedParser.lean"
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
