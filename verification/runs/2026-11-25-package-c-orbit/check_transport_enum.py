#!/usr/bin/env python3
"""
Task 3 (Issue #26 C2 closure):
Independent Python differential check comparing the exact executable transport-table
enumerator (`row_choices` / `table_choices` / `enum_tables`, mirroring Lean's
`TreeBudgetTransportEnum.lean`) against exhaustive enumeration of all m! permutations
for m = 0..4, checking BOTH:
  1. Set of cell-count tables
  2. Set of merged output histograms under g_in(a, b) = (a[0], a[1] + b[1])
"""

from collections import Counter
from fractions import Fraction
import itertools
import random


def K_in(a, b):
    return (not b[0]) or a[0]


def g_in(a, b):
    return (a[0], a[1] + b[1])


def row_choices(r, cols):
    if not cols:
        return [[]] if r == 0 else []
    (ok, cap), rest = cols[0], cols[1:]
    hi = min(r, cap) if ok else 0
    out = []
    for n in range(hi + 1):
        for tail in row_choices(r - n, rest):
            out.append([n] + tail)
    return out


def table_choices(K, bs, rows, caps):
    if not rows:
        return [[]] if all(c == 0 for c in caps) else []
    (a, r), rest_rows = rows[0], rows[1:]
    row_spec = [(K(a, b), c) for b, c in zip(bs, caps)]
    out = []
    for row in row_choices(r, row_spec):
        next_caps = [c - n for c, n in zip(caps, row)]
        for tail in table_choices(K, bs, rest_rows, next_caps):
            out.append([row] + tail)
    return out


def enum_tables(K, as_list, bs_list, x, y):
    rows = [(a, sum(1 for xi in x if xi == a)) for a in as_list]
    caps = [sum(1 for yj in y if yj == b) for b in bs_list]
    raw = table_choices(K, bs_list, rows, caps)
    return [tuple(tuple(r) for r in M) for M in raw]


def pushforward_hist(as_list, bs_list, M):
    cnt = Counter()
    for i, a in enumerate(as_list):
        for j, b in enumerate(bs_list):
            if M[i][j] > 0:
                cnt[g_in(a, b)] += M[i][j]
    return frozenset(cnt.items())


def exhaustive_perms(K, as_list, bs_list, x, y):
    m = len(x)
    a_idx = {a: i for i, a in enumerate(as_list)}
    b_idx = {b: j for j, b in enumerate(bs_list)}
    tables = set()
    hists = set()
    for perm in itertools.permutations(range(m)):
        if all(K(x[i], y[perm[i]]) for i in range(m)):
            M = [[0] * len(bs_list) for _ in range(len(as_list))]
            cnt = Counter()
            for i in range(m):
                a, b = x[i], y[perm[i]]
                M[a_idx[a]][b_idx[b]] += 1
                cnt[g_in(a, b)] += 1
            tables.add(tuple(tuple(r) for r in M))
            hists.add(frozenset(cnt.items()))
    return tables, hists


def check_case(name, K, as_list, bs_list, x, y):
    assert len(x) == len(y)
    assert len(set(as_list)) == len(as_list)
    assert len(set(bs_list)) == len(bs_list)
    enum_list = enum_tables(K, as_list, bs_list, x, y)
    enum_set = set(enum_list)
    assert len(enum_list) == len(enum_set), f"{name}: duplicate tables emitted!"
    enum_hists = {pushforward_hist(as_list, bs_list, M) for M in enum_set}
    perm_tables, perm_hists = exhaustive_perms(K, as_list, bs_list, x, y)
    assert enum_set == perm_tables, (
        f"{name}: table set mismatch!\n  enum={enum_set}\n  perm={perm_tables}"
    )
    assert enum_hists == perm_hists, (
        f"{name}: histogram set mismatch!\n  enum={enum_hists}\n  perm={perm_hists}"
    )
    return len(enum_set), len(enum_hists)


def main():
    cases = [
        # 1. m = 0 empty support
        ("m0_empty", K_in, [], [], [], []),
        # 2. m = 0 non-empty support (all zero multiplicities)
        (
            "m0_zero_mult_support",
            K_in,
            [(False, Fraction(0)), (True, Fraction(1))],
            [(False, Fraction(0)), (True, Fraction(1))],
            [],
            [],
        ),
        # 3. m = 1 zero-multiplicity type in support (Task 1 exact mirror)
        (
            "m1_zero_mult_support",
            lambda a, b: True,
            [(False, Fraction(0)), (True, Fraction(0))],
            [(False, Fraction(0)), (True, Fraction(0))],
            [(False, Fraction(0))],
            [(False, Fraction(0))],
        ),
        # 4. m = 4 repeated-type split-block (x = y = (u, u, v, v))
        (
            "m4_split_block",
            lambda a, b: True,
            [(False, Fraction(0)), (True, Fraction(1))],
            [(False, Fraction(0)), (True, Fraction(1))],
            [(False, Fraction(0)), (False, Fraction(0)), (True, Fraction(1)), (True, Fraction(1))],
            [(False, Fraction(0)), (False, Fraction(0)), (True, Fraction(1)), (True, Fraction(1))],
        ),
        # 5. Forbidden pairing causing infeasibility (K_in)
        (
            "m2_forbidden_infeasible",
            K_in,
            [(False, Fraction(0)), (True, Fraction(2))],
            [(True, Fraction(1)), (True, Fraction(-3, 2))],
            [(False, Fraction(0)), (True, Fraction(2))],
            [(True, Fraction(1)), (True, Fraction(-3, 2))],
        ),
        # 6. Multiple cells merging into the same output type (0+1 and 1+0 -> (True, 1))
        (
            "m2_output_type_merge",
            K_in,
            [(True, Fraction(0)), (True, Fraction(1))],
            [(True, Fraction(1)), (False, Fraction(0))],
            [(True, Fraction(0)), (True, Fraction(1))],
            [(True, Fraction(1)), (False, Fraction(0))],
        ),
        # 7. m = 4 signed rationals with K_in + zero-multiplicity extra types
        (
            "m4_signed_K_in_with_zeros",
            K_in,
            [(True, Fraction(-3, 2)), (True, Fraction(5, 2)), (False, Fraction(0)), (False, Fraction(7))],
            [(True, Fraction(1, 2)), (False, Fraction(-1, 2)), (False, Fraction(0)), (True, Fraction(9))],
            [(True, Fraction(-3, 2)), (True, Fraction(-3, 2)), (True, Fraction(5, 2)), (False, Fraction(0))],
            [(True, Fraction(1, 2)), (False, Fraction(-1, 2)), (False, Fraction(0)), (False, Fraction(0))],
        ),
    ]

    # Add randomized stress cases across m = 0..4
    rng = random.Random(20261128)
    pool = [
        (b, Fraction(n, 2))
        for b in (False, True)
        for n in (-3, -1, 0, 1, 2, 4)
    ]
    for m in range(5):
        for trial in range(12):
            x = [rng.choice(pool) for _ in range(m)]
            y = [rng.choice(pool) for _ in range(m)]
            # Include both exact supports and supersets with zero-multiplicity types
            extra_a = [rng.choice(pool)] if trial % 2 == 1 else []
            extra_b = [rng.choice(pool)] if trial % 3 == 1 else []
            as_list = list(dict.fromkeys(x + extra_a))
            bs_list = list(dict.fromkeys(y + extra_b))
            cases.append((f"rand_m{m}_t{trial}", K_in, as_list, bs_list, x, y))

    total_tables = 0
    total_hists = 0
    for name, K, as_list, bs_list, x, y in cases:
        nt, nh = check_case(name, K, as_list, bs_list, x, y)
        total_tables += nt
        total_hists += nh
        if not name.startswith("rand_"):
            print(f"[PASS] {name}: m={len(x)}, tables={nt}, output_hists={nh}")

    print(
        f"ALL {len(cases)} CASES PASSED "
        f"(m=0..4 exhaustive permutation check; total tables={total_tables}, total hists={total_hists})"
    )


if __name__ == "__main__":
    main()
