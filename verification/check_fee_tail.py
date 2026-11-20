"""Standard-library checks. Run with -h for the local Lean integration."""
from __future__ import annotations

import argparse
import itertools
import random
import re
import shutil
import subprocess
import tempfile
from collections import Counter
from dataclasses import dataclass, replace
from fractions import Fraction
from math import prod
from pathlib import Path

from fee_tail_stack import run_tail


def digits(n):
    return bin(n)[2:][::-1] if n else ""


def en(n):
    return "".join("1" + c for c in digits(n)) + "0"


def ez(z):
    return str(int(z < 0)) + en(abs(z))


def seq(enc, xs):
    return en(len(xs)) + "".join(map(enc, xs))


@dataclass(frozen=True)
class Fields:
    nums: tuple
    dens: tuple
    b: int
    q: int

    def bodies(self):
        return ("".join(map(ez, self.nums)), "".join(map(en, self.dens)), ez(self.b), en(self.q))

    def wire(self):
        return seq(ez, self.nums) + seq(en, self.dens) + ez(self.b) + en(self.q)


class Invalid(ValueError):
    pass


# Value-oriented oracle. Match a complete frame, decode integer, then round-trip.
FRAME = re.compile(r"(?:1[01])*0")


class Reader:
    def __init__(self, s):
        self.s = s
        self.i = 0

    def nat(self):
        match = FRAME.match(self.s, self.i)
        if match is None:
            raise Invalid
        frame = match.group()
        val = int(frame[1:-1:2][::-1] or "0", 2)
        if en(val) != frame:
            raise Invalid
        self.i = match.end()
        return val

    def integer(self):
        if self.i == len(self.s):
            raise Invalid
        neg = self.s[self.i] == "1"
        self.i += 1
        val = self.nat()
        if neg and not val:
            raise Invalid
        return -val if neg else val

    def many(self, read):
        k = self.nat()
        if k > len(self.s) - self.i:
            raise Invalid
        return tuple(read() for _ in range(k))


def tail_ref(n, s):
    p = Reader(s)
    try:
        f = Fields(p.many(p.integer), p.many(p.nat), p.integer(), p.nat())
    except Invalid:
        return None
    if p.i != len(s) or len(f.nums) != n or len(f.dens) != n or min((*f.dens, f.q)) <= 0:
        return None
    return f


@dataclass(frozen=True)
class Instance:
    m: int
    r: int
    ps: tuple
    hs: tuple
    f: Fields

    def prefix(self):
        return en(self.m) + en(len(self.ps)) + en(self.r) + seq(en, self.ps) + seq(en, self.hs)

    def wire(self):
        return self.prefix() + self.f.wire()


def read_instance(s):
    p = Reader(s)
    try:
        m, n, r = p.nat(), p.nat(), p.nat()
        ps, hs = p.many(p.nat), p.many(p.nat)
    except Invalid:
        return None
    if len(ps) != n or len(hs) != n or r >= n or max(ps) >= n or ps[r] != r:
        return None
    for v in range(n):
        seen = set()
        while v != r:
            if v in seen:
                return None
            seen.add(v)
            v = ps[v]
    if sum(hs[i] for i, parent in enumerate(ps) if i != r and parent == r) != m:
        return None
    f = tail_ref(n, s[p.i:])
    return Instance(m, r, ps, hs, f) if f is not None else None


def entry(e):
    c, row = e
    return en(c) + seq(en, row)


def read_cert(s, n):
    p = Reader(s)
    try:
        rows = p.many(lambda: (p.nat(), p.many(p.nat)))
    except Invalid:
        return None
    return rows if p.i == len(s) and all(len(row) == n for _, row in rows) else None


def row_budget(I, row, fees, budget):
    cost = 0
    for v, parent in enumerate(I.ps):
        if v != I.r:
            cost += (fees[v] + (fees[parent] if parent != I.r else 0)) * row[v]
    return cost <= budget


def integer_fees(f):
    # Prefix/suffix products avoid division, including with unreduced fractions.
    prefix = [1]
    for d in f.dens:
        prefix.append(prefix[-1] * d)
    scaled = [0] * len(f.nums)
    suffix = f.q
    for i in reversed(range(len(scaled))):
        scaled[i] = f.nums[i] * prefix[i] * suffix
        suffix *= f.dens[i]
    return scaled, f.b * prefix[-1]


def verifies(I, rows):
    if I is None or rows is None:
        return False
    n = len(I.ps)
    cols = [0] * n
    total = 0
    fees, budget = integer_fees(I.f)
    fractions = [Fraction(a, d) for a, d in zip(I.f.nums, I.f.dens)]
    den = I.f.q * prod(I.f.dens)
    if any(x != den * y for x,y in zip(fees, fractions)) or budget != den * Fraction(I.f.b, I.f.q):
        raise AssertionError("scaling mismatch")
    for c, row in rows:
        if len(row) != n or row[I.r] or any(row[v] > I.hs[v] for v in range(n) if v != I.r):
            return False
        if sum(row[v] for v in range(n) if v != I.r and I.ps[v] == I.r) != 1:
            return False
        if any(row[v] and not row[I.ps[v]] for v in range(n) if I.ps[v] != I.r and v != I.r):
            return False
        within = row_budget(I, row, fees, budget)
        rational = row_budget(I, row, fractions, Fraction(I.f.b, I.f.q))
        if within != rational:
            raise AssertionError("row cost mismatch")
        if not within:
            return False
        total += c
        for v, h in enumerate(row):
            cols[v] += c * h
    return total == I.m and all(cols[v] == I.hs[v] for v in range(n) if v != I.r)


def suffix_tests():
    counts = Counter()
    rng = random.Random(24038)

    def check(n, ps, s, ctx, group):
        ref = tail_ref(n, s)
        actual, saved, _ = run_tail(digits(n), "".join(map(en, ps)), n, s, ctx)
        expected = ref.bodies() if ref is not None else None
        if actual != expected or saved != ctx:
            raise AssertionError((n, s, actual, expected))
        counts[group, expected is not None] += 1

    for n in (0, 1, 2):
        for length in range(12):
            for bits in itertools.product("01", repeat=length):
                check(n, (0,) * n, "".join(bits), "101", "small")
    for n in (0, 1, 2, 4):
        for _ in range(60):
            f = Fields(tuple(rng.randrange(-8,9) for _ in range(n)),
                       tuple(rng.randrange(1,10) for _ in range(n)),
                       rng.randrange(-8,9), rng.randrange(1,10))
            s = f.wire()
            ps = tuple(range(n))
            cases = {s, s + "0", s + "1", en(2**128) + "101"}
            cases.update(s[:j] for j in range(len(s)))
            cases.update(s[:j] + str(1-int(s[j])) + s[j+1:] for j in range(len(s)))
            for case in sorted(cases):
                check(n, ps, case, "10" * 20, "edits")
    return counts


def corpus():
    items = []
    base = Instance(1,0,(0,0),(7,1),Fields((-2,0),(4,3),-3,6))
    # zero cost is greater than a negative budget
    row = ((1,(0,1)),)
    yes = replace(base, f=Fields((-2,-2),(4,4),-3,6))
    # -2/4 equals -3/6
    def add(tag,I,rows,p,v):
        x = I if isinstance(I,str) else I.wire()
        y = rows if isinstance(rows,str) else seq(entry,rows)
        J = read_instance(x)
        actual = (J is not None, verifies(J,read_cert(y,len(J.ps))) if J is not None else False)
        if actual != (p,v):
            raise AssertionError((tag,actual,p,v))
        items.append((tag,x,y,str(int(p)),str(int(v))))
    add("negative_budget_reject",base,row,True,False)
    add("unreduced_equality",yes,row,True,True)
    add("legal_zero",yes,row+((0,(0,1)),),True,True)
    add("invalid_zero",yes,row+((0,(0,0)),),True,False)
    add("duplicate",replace(yes,m=2,hs=(7,2)),row+row,True,True)
    add("wrong_row_length",yes,((1,(1,)),),True,False)
    add("bad_col",replace(yes,m=2,hs=(7,2)),row,True,False)
    add("huge_m",replace(yes,m=2**90,hs=(7,2**90)),((2**90,(0,1)),),True,True)
    add("huge_mismatch",yes,((2**100,(0,1)),),True,False)
    chain = Instance(1,1,(1,1,0),(1,2**80,3),Fields((2,9,-3),(4,1,2),-5,2))
    # 1/2 + 3*(-3/2+1/2) = -5/2, grandchild > parent is legal
    add("nonzero_root_parent_fee",chain,((1,(1,0,3)),),True,True)
    add("missed_equality",replace(chain,f=replace(chain.f,b=-6)),((1,(1,0,3)),),True,False)
    split=Instance(2,0,(0,0,0),(0,1,1),Fields((0,0,0),(1,1,1),0,1))
    add("wrong_column_correct_total",split,((2,(0,1,0)),),True,False)
    disconnected=Instance(1,0,(0,0,0,1),(0,0,1,1),Fields((0,0,0,0),(1,1,1,1),0,1))
    add("missing_parent_support",disconnected,((1,(0,0,1,1)),),True,False)
    add("root_only_empty",Instance(0,0,(0,),(17,),Fields((-2,),(4,),-2,4)),(),True,True)
    add("cert_trailing",yes,seq(entry,row)+"0",True,False)
    add("cert_huge_count",yes,en(2**120)+"11",True,False)
    add("cert_truncated",yes,seq(entry,row)[:-1],True,False)
    add("instance_trailing",yes.wire()+"0",row,False,False)
    add("empty_tail",yes.prefix(),row,False,False)
    add("wrong_routes",replace(yes,m=2),row,False,False)
    add("independent_cycle",replace(yes,ps=(0,1)),row,False,False)
    add("bad_root",replace(yes,r=9),row,False,False)
    add("wrong_H_length",replace(yes,hs=(1,)),row,False,False)
    add("fee_dim",replace(yes,f=replace(yes.f,nums=(1,))),row,False,False)
    add("den_dim",replace(yes,f=replace(yes.f,dens=(1,))),row,False,False)
    add("zero_root_den",replace(yes,f=replace(yes.f,dens=(0,1))),row,False,False)
    add("zero_budget_den",replace(yes,f=replace(yes.f,q=0)),row,False,False)
    add("negative_zero",yes.prefix()+en(2)+"10"+ez(2)+seq(en,(4,4))+ez(-3)+en(6),row,False,False)
    add("padded_fee_word",yes.prefix()+en(2)+"0"+"100"+ez(2)+seq(en,(4,4))+ez(-3)+en(6),row,False,False)
    add("huge_short_fee_count",yes.prefix()+en(2**100)+"101",row,False,False)
    # All possible single-bit mutations and all strict truncations for one entire instance.
    x, y = yes.wire(), seq(entry,row)
    for j in range(len(x)):
        for tag, xx in (("flip",x[:j]+str(1-int(x[j]))+x[j+1:]),("cut",x[:j])):
            J = read_instance(xx)
            rows = read_cert(y,len(J.ps)) if J else None
            add(f"{tag}_{j}",xx,y,J is not None,verifies(J,rows))
    return items


def small_matrices():
    # Exhaust all labelled rooted trees on 1–3 vertices, nonroot H in 0..2,
    # and their compatible m <= 2. Compare two independently enumerated spaces.
    stats = Counter()
    for n in (1, 2, 3):
        for ps in itertools.product(range(n), repeat=n):
            for r in range(n):
                if ps[r] != r:
                    continue
                def reaches_root(v):
                    for _ in range(n):
                        v = ps[v]
                    return v == r
                if not all(map(reaches_root, range(n))):
                    continue
                nonroot = [v for v in range(n) if v != r]
                for hs_small in itertools.product(range(3), repeat=n-1):
                    hs = [7] * n
                    for v,h in zip(nonroot,hs_small):
                        hs[v] = h
                    m = sum(hs[v] for v in nonroot if ps[v] == r)
                    if m > 2:
                        continue
                    choices = [range(1) if v == r else range(hs[v]+1) for v in range(n)]
                    grid = list(itertools.product(*choices))
                    costs = ((tuple(0 for _ in ps), 0),
                             (tuple(2*v-3 for v in range(n)), -1),
                             (tuple(3-2*v for v in range(n)), 1))
                    for nums,b in costs:
                        f = Fields(nums, tuple(v+2 for v in range(n)), b, 2)
                        I = Instance(m,r,ps,tuple(hs),f)
                        fees = tuple(Fraction(a,d) for a,d in zip(nums,f.dens))
                        budget = Fraction(b,2)
                        A,T = integer_fees(f)
                        direct, linear = [], []
                        for row in grid:
                            if sum(row[v] for v in nonroot if ps[v] == r) != 1:
                                continue
                            if (all(not row[v] or row[ps[v]] for v in nonroot if ps[v] != r)
                                    and row_budget(I,row,fees,budget)):
                                direct.append(row)
                            if (all(row[v] <= hs[v]*row[ps[v]] for v in nonroot if ps[v] != r)
                                    and row_budget(I,row,A,T)):
                                linear.append(row)
                        if direct != linear:
                            raise AssertionError(("row polytope",I))
                        feasible = any(all(sum(row[v] for row in matrix) == hs[v] for v in nonroot)
                                       for matrix in itertools.product(direct,repeat=m))
                        best = None
                        for cs in itertools.product(range(m+1), repeat=len(linear)):
                            if sum(cs) != m:
                                continue
                            rows = tuple((c,row) for c,row in zip(cs,linear) if c)
                            if not all(sum(c*row[v] for c,row in rows) == hs[v] for v in nonroot):
                                continue
                            y = seq(entry,rows)
                            if not verifies(I,read_cert(y,n)):
                                raise AssertionError(("certificate wire",I,rows))
                            if best is None or (len(rows),len(y)) < best:
                                best = len(rows),len(y)
                        if feasible != (best is not None):
                            raise AssertionError(("matrix / compressed", I))
                        if best is not None:
                            k,w = best
                            L = len(I.wire())
                            if not (2**k <= (m+1)*prod(hs[v]+1 for v in nonroot)
                                    and k <= 2**(n-1) and w <= L*(L//2+1)):
                                raise AssertionError(("sparse bounds",I,k,w))
                        stats[feasible] += 1
    return stats


def check_audits(log):
    groups = {
        "A4FeeTailSpec": ("prefix_append", "prefix_canonical", "read_iff", "good_iff",
                          "rebuild_wire", "parseInstance_finish"),
        "A4FeeTailChecks": ("saved_outputs", "rejects_zero_denominator", "rejects_trailing",
                            "raw_start_accepts", "raw_start_rejects_trailing", "standard_init_accepts", "raw_start_wrong_routes"),
    }
    check_named_audits(log, ["UAVProof." + group + "." + name
                             for group, names in groups.items() for name in names])


def check_named_audits(log, names):
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for full in names:
        pattern = (r"'" + re.escape(full) +
                   r"'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])")
        match = re.search(pattern, log)
        if not match:
            raise SystemExit("Missing axiom report for " + full)
        used = {a.strip() for a in (match.group(1) or "").split(",") if a.strip()}
        if used - allowed:
            raise SystemExit("Unexpected axioms in " + full + ": " + str(used - allowed))


def checked_lean_output(cmd, repo):
    # Decode Lean output explicitly on Windows, including older console code pages.
    proc = subprocess.run(cmd, cwd=repo, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = proc.stdout.decode("utf-8", errors="replace")
    import sys
    sys.stdout.buffer.write(log.encode(sys.stdout.encoding or "utf-8", errors="backslashreplace"))
    sys.stdout.flush()
    if proc.returncode or "sorryAx" in log or "declaration uses 'sorry'" in log:
        raise SystemExit(proc.returncode or 1)
    return log


def project_import_closure(repo, roots):
    """All repository-owned LeanCompletion imports, excluding pinned external packages."""
    seen = set()
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module in seen or not module.startswith("LeanCompletion."):
            continue
        source = repo.joinpath(*module.split(".")).with_suffix(".lean")
        if not source.is_file():
            raise SystemExit("Missing project import source: " + module)
        seen.add(module)
        for line in source.read_text(encoding="utf-8-sig").splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+)$", line)
            if match:
                pending.extend(name for name in match.group(1).split("--", 1)[0].split()
                               if name.startswith("LeanCompletion."))
    return sorted(seen)


def run_lean(repo, records, skip_build=False):
    repo = repo.resolve()
    lake = shutil.which("lake")
    if not lake:
        raise SystemExit("Lake unavailable. Install/use the repository-pinned local toolchain.")
    required = repo / "LeanCompletion/UAV/TreeBudgetRootFlowTotal.lean"
    if not required.is_file():
        raise SystemExit("Pass --repo with the research checkout containing TreeBudgetRootFlowTotal.lean")
    here = Path(__file__).resolve().parent
    audit = here / "AuditTreeBudgetInstanceEntry.lean"
    audit_lines = audit.read_text(encoding="utf-8").splitlines()
    modules = [line.removeprefix("import ").strip() for line in audit_lines if line.startswith("import ")]
    names = [line.removeprefix("#print axioms ").strip() for line in audit_lines
             if line.startswith("#print axioms ")]
    if not modules or not names:
        raise SystemExit("The explicit instance-entry audit is empty")
    # Lake's targeted build refreshes stale project modules and reuses available caches.
    if not skip_build:
        subprocess.run([lake, "build", *["+" + module for module in modules]], cwd=repo, check=True)
    else:
        stale = []
        project_modules = project_import_closure(repo, modules)
        for module in project_modules:
            src = repo.joinpath(*module.split(".")).with_suffix(".lean")
            obj = (repo / ".lake/build/lib/lean").joinpath(*module.split(".")).with_suffix(".olean")
            if not obj.exists() or obj.stat().st_mtime < src.stat().st_mtime:
                stale.append(module)
        if stale:
            raise SystemExit("Missing/stale prebuilt project modules:\n" + "\n".join(stale))
        print(f"Prebuilt project dependency closure: {len(project_modules)} modules current.", flush=True)
    audit_log = checked_lean_output([lake, "env", "lean", "--root=" + str(here), str(audit)], repo)
    check_named_audits(audit_log, names)
    print(f"Full instance-entry audit: {len(names)} named declarations checked.", flush=True)
    local_runs = repo / "verification/runs"
    local_runs.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="a4-fee-", dir=local_runs) as d:
        tmp = Path(d)
        source = here / "RunTreeBudgetFeeTail.lean"
        data = tmp / "cases.tsv"
        data.write_bytes("".join("\t".join(case)+"\n" for case in records).encode("ascii"))
        cmd = [lake, "env", "lean", "--root=" + str(here), "--run", str(source), str(data)]
        log = checked_lean_output(cmd, repo)
        check_audits(log)
        expected = "Lean reference, composed instance machine and context agree on "
        if expected + str(len(records)) + " cases." not in log:
            raise SystemExit("Missing Lean completion record")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="run the local Lake build, kernel checks and corpus")
    parser.add_argument("--skip-build", action="store_true", help="use explicitly prebuilt current modules for --lean")
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="root of the existing Lean checkout")
    args = parser.parse_args()
    checked = suffix_tests()
    for group in sorted({g for g,_ in checked}):
        print(f"{group}: {checked[group,True]} accept, {checked[group,False]} reject")
    matrices = small_matrices()
    print(f"Small matrix vs compressed: {matrices[True]} feasible, {matrices[False]} infeasible.")
    records = corpus()
    print(f"Python instance/certificate corpus: {len(records)} cases, "
          f"{sum(p=='1' for _,_,_,p,_ in records)} parsed, "
          f"{sum(v=='1' for *_,v in records)} verified.", flush=True)
    if args.lean:
        run_lean(args.repo, records, args.skip_build)


if __name__ == "__main__":
    main()
