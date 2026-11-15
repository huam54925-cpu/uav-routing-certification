#!/usr/bin/env python3
"""Finite reference checks for the F1--F3 design; standard library only.

This is an independent Python model, NOT execution or validation of Lean code.
It compares ordered tables INCLUDING payloads, selected certificates, and a
separate exhaustive matrix feasibility test on increasing rooted trees.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import lcm
import json


def compositions(m, h):
    if m == 0:
        return [()] if h == 0 else []
    return [(a,) + tail for a in range(h + 1)
            for tail in compositions(m - 1, h - a)]


def dedup_right(xs, key):
    seen, out = set(), []
    for x in reversed(xs):
        k = key(x)
        if k not in seen:
            seen.add(k)
            out.append(x)
    return list(reversed(out))


@dataclass(frozen=True)
class Entry:
    active: tuple
    cost: tuple
    matrix: tuple


@dataclass(frozen=True)
class Root:
    used: tuple
    cost: tuple
    picks: tuple


def children(parent, v):
    return [u for u in range(1, len(parent)) if parent[u] == v]


def linear_weights(parent, service):
    return tuple(Q(0) if v == 0 else service[v] +
                 (Q(0) if parent[v] == 0 else service[parent[v]])
                 for v in range(len(parent)))


def prepare(parent, service):
    a = linear_weights(parent, service)
    D = 1
    for x in a:
        D = lcm(D, x.denominator)
    w = tuple((D // x.denominator) * x.numerator for x in a)
    assert D > 0 and w[0] == 0
    assert all(Q(z) == D * x for z, x in zip(w, a))
    return a, D, w


def glue(n, m, v, q, picks):
    return tuple(tuple(q[i] if x == v else sum(e.matrix[i][x] for e in picks)
                       for x in range(n)) for i in range(m))


def run_tables(parent, H, weights, m):
    n, tables = len(parent), {}

    def inside(active, base, ts):
        if not ts:
            return [(base, ())]
        rest = inside(active, base, ts[1:])
        raw = [(tuple(x + y for x, y in zip(e.cost, cost)), (e,) + picks)
               for e in ts[0]
               if all(not x or y for x, y in zip(e.active, active))
               for cost, picks in rest]
        return dedup_right(raw, lambda r: r[0])

    def compute(v):
        ts = [compute(u) for u in children(parent, v)]
        raw = []
        for q in compositions(m, H[v]):
            if parent[v] == 0 and any(x > 1 for x in q):
                continue
            active = tuple(x > 0 for x in q)
            base = tuple(weights[v] * x for x in q)
            for cost, picks in inside(active, base, ts):
                raw.append(Entry(active, cost, glue(n, m, v, q, picks)))
        tables[v] = dedup_right(raw, lambda e: (e.active, e.cost))
        return tables[v]

    def roots(ts):
        if not ts:
            return [Root((0,) * m, (0,) * m, ())]
        rest = roots(ts[1:])
        raw = []
        for e in ts[0]:
            for r in rest:
                used = tuple(x + int(y) for x, y in zip(r.used, e.active))
                cost = tuple(x + y for x, y in zip(r.cost, e.cost))
                if all(x <= 1 for x in used):
                    raw.append(Root(used, cost, (e,) + r.picks))
        return dedup_right(raw, lambda r: (r.used, r.cost))

    rs = roots([compute(u) for u in children(parent, 0)])
    return tables, rs


def lift_entry(e, D):
    return Entry(e.active, tuple(Q(x, D) for x in e.cost), e.matrix)


def lift_root(r, D):
    return Root(r.used, tuple(Q(x, D) for x in r.cost),
                tuple(lift_entry(e, D) for e in r.picks))


def solve_from_roots(n, m, rs, budget):
    for r in rs:
        if all(u == 1 and c <= budget for u, c in zip(r.used, r.cost)):
            return glue(n, m, 0, (0,) * m, r.picks)
    return None


def structural_matrices(parent, H, m):
    """No DP or deduplication: enumerate every column assignment directly."""
    n = len(parent)
    for columns in product(*(compositions(m, H[v]) for v in range(1, n))):
        mat = tuple((0,) + tuple(col[i] for col in columns) for i in range(m))
        if any(sum(row[v] for v in children(parent, 0)) != 1 for row in mat):
            continue
        if any(row[v] > 0 and parent[v] != 0 and row[parent[v]] == 0
               for row in mat for v in range(1, n)):
            continue
        yield mat


def valid_certificate(parent, H, service, m, T, mat):
    if mat is None or len(mat) != m:
        return False
    n = len(parent)
    if any(len(row) != n or row[0] != 0 for row in mat):
        return False
    if any(sum(row[v] for row in mat) != H[v] for v in range(1, n)):
        return False
    for row in mat:
        if sum(row[v] for v in children(parent, 0)) != 1:
            return False
        if any(row[v] > 0 and parent[v] != 0 and row[parent[v]] == 0
               for v in range(1, n)):
            return False
        direct = sum(service[v] * (row[v] + sum(row[u] for u in children(parent, v)))
                     for v in range(1, n))
        linear = sum(a * x for a, x in zip(linear_weights(parent, service), row))
        assert direct == linear
        if direct > T:
            return False
    return True


def main():
    counts = dict(table_instances=0, scaled_table_comparisons=0,
                  budget_instances=0, certificate_equalities=0,
                  feasible_instances=0, root_fee_invariance=0)
    budgets = [Q(-3, 2), Q(-1, 6), Q(0), Q(1, 2), Q(3), Q(10)]
    for n in range(1, 5):
        for ps in product(*(range(v) for v in range(1, n))):
            parent = (0,) + ps
            profiles = [tuple(Q(0) for _ in range(n)),
                        tuple(Q(v + 1, 3) for v in range(n)),
                        tuple(Q((-1) ** v * (v + 2), 4) for v in range(n)),
                        tuple(Q(7, 5) if v % 2 else Q(-11, 6) for v in range(n)),
                        tuple(Q(v - 2, 7) for v in range(n))]
            for hs in product(range(3), repeat=n - 1):
                H = (987,) + hs  # irrelevant root coordinate intentionally nonzero
                for m in range(4):
                    brute = list(structural_matrices(parent, H, m))
                    for service in profiles:
                        a, D, w = prepare(parent, service)
                        tq, rq = run_tables(parent, H, a, m)
                        counts['table_instances'] += 1
                        changed = (Q(123, 97),) + service[1:]
                        assert prepare(parent, changed) == (a, D, w)
                        counts['root_fee_invariance'] += 1
                        scaled = []
                        for k in (1, 2, 5):
                            Dk = k * D
                            tz, rz = run_tables(parent, H, tuple(k * x for x in w), m)
                            assert {v: [lift_entry(e, Dk) for e in es]
                                    for v, es in tz.items()} == tq
                            assert [lift_root(r, Dk) for r in rz] == rq
                            counts['scaled_table_comparisons'] += 1
                            scaled.append((Dk, rz))
                        for T in budgets:
                            cert = solve_from_roots(n, m, rq, T)
                            feasible = any(valid_certificate(parent, H, service, m, T, z)
                                           for z in brute)
                            assert (cert is not None) == feasible
                            if cert is not None:
                                assert valid_certificate(parent, H, service, m, T, cert)
                                counts['feasible_instances'] += 1
                            for Dk, rz in scaled:
                                DT = Dk * T
                                B = DT.numerator // DT.denominator
                                assert solve_from_roots(n, m, rz, B) == cert
                                counts['certificate_equalities'] += 1
                            counts['budget_instances'] += 1
    assert dedup_right([(0, 'left'), (0, 'right')], lambda x: x[0]) == [(0, 'right')]
    assert (-3 // 2) == -2 and int(Q(-3, 2)) == -1
    assert not (-1 <= (-3 // 2)) and (-1 <= int(Q(-3, 2)))
    print(json.dumps({'result': 'PASS', 'scope': 'independent finite Python model',
                      'counts': counts}, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
