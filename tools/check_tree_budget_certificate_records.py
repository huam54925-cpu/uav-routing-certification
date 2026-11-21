"""Differential checks for #24 certificate syntax and the proved TM2 parser.

Adapted from the user-supplied A4_certificate_records_local.zip.
Python models do not count TM2 transitions; the Lean driver enforces recordBound.
"""
from __future__ import annotations

import argparse
import itertools
import random
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


def digits(n):
    return bin(n)[2:][::-1] if n else ""


def nat(n):
    return "".join("1"+b for b in digits(n))+"0"


def entry(c, row):
    return nat(c)+nat(len(row))+"".join(map(nat,row))


def wire(records):
    return nat(len(records))+"".join(entry(c,row) for c,row in records)


class Bad(ValueError):
    pass


# Reference parser matches a whole word, reconstructs the number, and
# re-encodes it to reject high zero digits. Row length is checked at the end.
FRAME = re.compile(r"(?:1[01])*0")
def reference(n,y):
    i=0
    def read():
        nonlocal i
        m=FRAME.match(y,i)
        if not m:
            raise Bad
        w=m.group()
        a=int(w[1:-1:2][::-1] or "0",2)
        if w!=nat(a):
            raise Bad
        i=m.end()
        return a
    def counted(f):
        k=read()
        if k>len(y)-i:
            raise Bad
        return tuple(f() for _ in range(k))
    try:
        rows=counted(lambda: (read(),counted(read)))
    except Bad:
        return None
    if i!=len(y) or any(len(row)!=n for _,row in rows):
        return None
    return rows


# Stack-oriented independent prototype. It models the data contracts of the
# existing subroutines, without claiming to count individual Lean transitions.
def frame(src):
    result=[]
    while src:
        if src.pop()=="0":
            if result and result[-1]!="1":
                raise Bad
            return result
        if not src:
            raise Bad
        result.append(src.pop())
    raise Bad


def guarded_ticks(src):
    count=list(reversed(frame(src)))
    moved=[]
    # Destructive binary decrement with underflow. Permit padded intermediate digits.
    while True:
        borrow=[]
        while count and count[-1]=="0":
            count.pop()
            borrow.append("1")
        if not count:
            break
        count[-1]="0"
        count.extend(borrow)
        if not src:
            raise Bad
        moved.append(src.pop())
    tokens=[]
    while moved:
        src.append(moved.pop())
        tokens.append(True)
    return tokens


def binary_inc(counter):
    # stack top = least significant bit
    scratch=[]
    while counter and counter[-1]=="1":
        counter.pop()
        scratch.append("0")
    if counter:
        counter.pop()
    counter.append("1")
    counter.extend(scratch)


@dataclass(frozen=True)
class Run:
    payload: tuple | None
    entries_called: int
    dimension: str
    context: str


def prototype(n,y,ctx):
    dim=digits(n)
    protected=tuple(ctx)
    entered=0
    try:
        header=list(reversed(y))
        saved=guarded_ticks(header)
        todo=saved.copy()
        cursor=header.copy()
        while todo:
            todo.pop()
            entered+=1
            frame(cursor)  # binary multiplicity, including zero
            inner=guarded_ticks(cursor)
            row=[]
            while inner:
                inner.pop()
                coordinate=frame(cursor)
                for digit in coordinate:
                    row.extend(("1",digit))
                row.append("0")
            counter=[]
            body=list(reversed(row))
            while body:
                if body.pop()=="1":
                    body.pop()  # a payload bit
                else:
                    binary_inc(counter)
            if list(reversed(counter))!=list(dim):
                raise Bad
        if cursor:
            raise Bad
        payload=(len(saved),"".join(reversed(header)))
    except Bad:
        payload=None
    return Run(payload,entered,dim,"".join(protected))


def validate(n,y,ctx):
    rows=reference(n,y)
    got=prototype(n,y,ctx)
    expected=None if rows is None else (len(rows),"".join(entry(c,row) for c,row in rows))
    if (got.payload,got.dimension,got.context)!=(expected,digits(n),ctx):
        raise AssertionError((n,y,expected,got))
    return rows is not None,got


def named_cases():
    x=((2,(0,5)),(0,(1,0)),(2,(0,5)))
    good=wire(x)
    return [
        ("zero_exact",4,wire(()),True),
        ("zero_trailing",4,wire(())+"0",False),
        ("empty_input",2,"",False),
        ("saved_order_zero_duplicate",2,good,True),
        ("last_trailing",2,good+"1",False),
        ("cut_second",2,nat(2)+entry(5,(3,0))+nat(0)+"1",False),
        ("outer_oversize",2,nat(2**90)+"101",False),
        ("huge_multiplicity",2,wire(((2**90,(0,0)),)),True),
        ("inner_oversize",1,nat(1)+nat(0)+nat(2**90)+"101",False),
        ("short_row",2,wire(((0,(1,)),)),False),
        ("long_row",1,wire(((0,(1,0)),)),False),
        ("noncanonical_count",0,"100",False),
        ("noncanonical_coordinate",1,nat(1)+nat(5)+nat(1)+"100",False),
        ("dimension_zero",0,wire(((0,()),(7,()))),True),
        ("huge_dimension_empty",2**120,wire(()),True),
        ("huge_dimension_short_row",2**120,wire(((0,(0,)),)),False),
        ("huge_coordinate",1,wire(((0,(2**120,)),)),True),
        ("two_same_mult_different_rows",2,wire(((3,(1,0)),(3,(0,1)))),True),
        ("prefix_borrows_to_zero",2,nat(8)+"10101010",False),
        ("header_cut",1,"11",False),
        ("syntax_valid_semantic_bad",2,wire(((0,(0,0)),)),True),
    ]


def suite():
    corp=[]
    counts=Counter()
    def check(group,tag,n,y,ctx,expected=None,keep=False):
        ok,got=validate(n,y,ctx)
        counts[group,ok]+=1
        if expected is not None and ok!=expected:
            raise AssertionError((tag,n,y))
        if tag=="outer_oversize" and got.entries_called!=0:
            raise AssertionError("entered record loop after failed count guard")
        if tag=="huge_multiplicity" and got.entries_called!=1:
            raise AssertionError("expanded a binary multiplicity")
        if keep:
            corp.append((tag,str(n),y,ctx,str(int(ok))))
    for t,n,y,ok in named_cases():
        check("named",t,n,y,"011010",ok,True)
    for n in (0,1,2,3):
        for length in range(13):
            for bits in itertools.product("01",repeat=length):
                check("exhaustive","short",n,"".join(bits),"101")
    rng=random.Random(75124)
    for i in range(96):
        n=rng.randrange(5)
        rows=tuple((rng.randrange(13),tuple(rng.randrange(9) for _ in range(n)))
                   for _ in range(rng.randrange(1,5)))
        y=wire(rows)
        ctx="".join(rng.choice("01") for _ in range(rng.randrange(12)))
        tests=[y,y+"0",y+"1"]
        tests.extend(y[:j] for j in range(len(y)))
        tests.extend(y[:j]+("1" if c=="0" else "0")+y[j+1:] for j,c in enumerate(y))
        pick={0,1,2,3+rng.randrange(len(y)),3+len(y)+rng.randrange(len(y))}
        for j,test in enumerate(tests):
            check("mutations",f"field_{i}_{j}",n,test,ctx,True if j==0 else None,j in pick)
    return counts,corp


def run_lean(repo, corpus, no_build):
    lake = shutil.which("lake")
    if not lake:
        raise SystemExit("No Lake executable found on PATH.")
    driver = repo / "verification/RunTreeBudgetCertificateRecords.lean"
    audit = repo / "verification/AuditTreeBudgetCertificateRecords.lean"
    if not driver.is_file() or not audit.is_file():
        raise SystemExit("Select the checkout containing the certificate-record proofs.")
    runs = repo / "verification/runs/certificate-records"
    runs.mkdir(parents=True, exist_ok=True)

    def execute(args, log_name):
        result = subprocess.run([lake, *args], cwd=repo, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        (runs / log_name).write_bytes(result.stdout)
        text = result.stdout.decode("utf-8", errors="replace")
        if result.returncode or "sorryAx" in text or "declaration uses 'sorry'" in text:
            raise SystemExit(f"Failed {log_name}; inspect {runs / log_name}")
        return text

    if not no_build:
        execute(["build", "+LeanCompletion.UAV.TreeBudgetCertificateRecordsTotal",
                 "+LeanCompletion.UAV.TreeBudgetCertificateRecordsExamples"], "build.log")
    with tempfile.TemporaryDirectory(prefix="corpus-", dir=runs) as temp:
        cases = Path(temp) / "cases.tsv"
        cases.write_bytes("".join("\t".join(row) + "\n" for row in corpus).encode("ascii"))
        text = execute(["env", "lean", "--run", str(driver), str(cases)], "lean-corpus.log")
    marker = f"record machine and repository decoder agree on {len(corpus)} cases"
    if marker not in text:
        raise SystemExit("Missing Lean corpus completion record.")
    print(marker, flush=True)
    text = execute(["env", "lean", str(audit)], "axioms.log")
    names = re.findall(r"^#print axioms (\S+)$", audit.read_text(encoding="utf-8"), re.M)
    if len(names) != len(set(names)):
        raise SystemExit("Duplicate explicit declaration in the audit source.")
    for name in names:
        pattern = r"'" + re.escape(name) + r"'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
        match = re.search(pattern, text)
        if not match:
            raise SystemExit("Missing audit for " + name)
        used = {a.strip() for a in (match.group(1) or "").split(",") if a.strip()}
        if used - {"propext", "Classical.choice", "Quot.sound"}:
            raise SystemExit("Unexpected axioms for " + name)
    print(f"Axiom audit: {len(names)} declarations passed.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="also check the actual machine and axioms")
    parser.add_argument("--no-build", action="store_true", help="reuse already-built pinned Lean modules")
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="research repository root")
    args = parser.parse_args()
    counts, corpus = suite()
    for group in sorted({key[0] for key in counts}):
        print(f"{group}: {counts[group,True]} accepted, {counts[group,False]} rejected")
    print(f"Python: {sum(counts.values())} comparisons; {len(corpus)} corpus rows prepared for Lean.", flush=True)
    if args.lean:
        run_lean(args.repo.resolve(), corpus, args.no_build)


if __name__ == "__main__":
    main()
