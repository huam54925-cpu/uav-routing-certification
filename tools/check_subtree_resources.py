#!/usr/bin/env python3
"""Independent, finite source-level resource model; no Lean/runtime timing claims.
Copy beside tools/check_subtree_auto_cert.py, or pass --baseline PATH.
Python standard library only. Integer values have unbounded precision.
"""
import argparse
import copy
import importlib.util
import json
import sys
from fractions import Fraction as Q
from itertools import product
from math import comb, lcm, prod
from pathlib import Path

KEY_FIELDS = ('nodeCalls compositionCalls rangeChoices columnsGenerated columnsAccepted '
              'subsetCalls insidePairs rootPairs rootRejected ratAdds ratMuls dedupInput '
              'dedupOutput eqCalls acceptCalls maxRawTable maxDedupTable').split()
PAYLOAD_FIELDS = ('matrices matrixCells childReads natAdds tempCells columnReads '
                  'pickCons keyMapCells rootZeroCells').split()


class Meter:
    def __init__(self):
        self.key = dict.fromkeys(KEY_FIELDS, 0)
        self.payload = dict.fromkeys(PAYLOAD_FIELDS, 0)
        self.raw_by_vertex = {}
        self.dedup_lengths = []
        self.max_abs_cost = 0
        self.max_nat_cell = 0

    def bump(self, name, k=1):
        self.key[name] += k

    def cost(self, xs):
        self.max_abs_cost = max([self.max_abs_cost] + [abs(x) for x in xs])
        return tuple(xs)

    def dedup(self, xs, key):
        # Reverse traversal implements tail-first recursion. Lists here are a
        # mathematical model: Python list copying is not charged as Lean cons.
        out = []
        self.dedup_lengths.append(len(xs))
        self.bump('dedupInput', len(xs))
        self.key['maxRawTable'] = max(self.key['maxRawTable'], len(xs))
        for x in reversed(xs):
            keys = [key(y) for y in out]
            self.payload['keyMapCells'] += len(keys)
            found = False
            for k in keys:
                self.bump('eqCalls')
                if key(x) == k:
                    found = True
                    break
            if not found:
                out = [x] + out
        self.bump('dedupOutput', len(out))
        self.key['maxDedupTable'] = max(self.key['maxDedupTable'], len(out))
        return out


def counted_tables(ref, parent, H, w, m, root=0):
    nV, meter, tables = len(parent), Meter(), {}

    def children(v):
        return [u for u in range(nV) if u != root and parent[u] == v]

    def compositions(m0, h):
        meter.bump('compositionCalls')
        if m0 == 0:
            return [()] if h == 0 else []
        meter.bump('rangeChoices', h + 1)
        return [(a,) + tail for a in range(h + 1) for tail in compositions(m0 - 1, h - a)]

    def inside(active, base, ts):
        if not ts:
            meter.key['maxRawTable'] = max(meter.key['maxRawTable'], 1)
            meter.key['maxDedupTable'] = max(meter.key['maxDedupTable'], 1)
            return [(base, ())]
        rest = inside(active, base, ts[1:])
        meter.bump('subsetCalls', len(ts[0]))
        raw = []
        for e in ts[0]:
            if not all(not x or y for x, y in zip(e.active, active)):
                continue
            for cost, picks in rest:
                meter.bump('insidePairs')
                meter.bump('ratAdds', m)
                meter.payload['pickCons'] += 1
                raw.append((meter.cost([x + y for x, y in zip(e.cost, cost)]), (e,) + picks))
        return meter.dedup(raw, lambda r: r[0])

    def compute(v):
        meter.bump('nodeCalls')
        ts = [compute(u) for u in children(v)]
        all_q = compositions(m, H[v])
        meter.bump('columnsGenerated', len(all_q))
        qs = [q for q in all_q if parent[v] != root or all(x <= 1 for x in q)]
        meter.bump('columnsAccepted', len(qs))
        raw = []
        for q in qs:
            active = tuple(x > 0 for x in q)
            meter.bump('ratMuls', m)
            base = meter.cost([w[v] * x for x in q])
            for cost, picks in inside(active, base, ts):
                matrix = counted_glue(ref, parent, H, m, v, q, picks, meter, root)
                raw.append(ref.Entry(active, cost, matrix))
        meter.raw_by_vertex[v] = len(raw)
        tables[v] = meter.dedup(raw, lambda e: (e.active, e.cost))
        return tables[v]

    def roots(ts):
        if not ts:
            meter.key['maxRawTable'] = max(meter.key['maxRawTable'], 1)
            meter.key['maxDedupTable'] = max(meter.key['maxDedupTable'], 1)
            return [ref.Root((0,) * m, (0,) * m, ())]
        rest = roots(ts[1:])
        kept, raw_count = [], 0
        for e in ts[0]:
            for r in rest:
                raw_count += 1
                meter.bump('rootPairs')
                meter.bump('ratAdds', m)
                meter.payload['pickCons'] += 1
                used = tuple(x + int(y) for x, y in zip(r.used, e.active))
                assert all(x <= 2 for x in used)
                cost = meter.cost([x + y for x, y in zip(r.cost, e.cost)])
                if all(x <= 1 for x in used):
                    kept.append(ref.Root(used, cost, (e,) + r.picks))
                else:
                    meter.bump('rootRejected')
        meter.key['maxRawTable'] = max(meter.key['maxRawTable'], raw_count)
        return meter.dedup(kept, lambda r: (r.used, r.cost))

    rs = roots([compute(v) for v in children(root)])
    return tables, rs, meter


def counted_glue(ref, parent, H, m, v, q, picks, meter, root=0):
    meter.payload['matrices'] += 1
    mat = []
    for i in range(m):
        row = []
        for x in range(len(parent)):
            if x == v:
                meter.payload['columnReads'] += 1
                value = q[i]
            else:
                temp = []
                for e in picks:
                    meter.payload['childReads'] += 1
                    meter.payload['tempCells'] += 1
                    temp.append(e.matrix[i][x])
                value = 0
                for a in temp:
                    meter.payload['natAdds'] += 1
                    value += a
                    assert value <= (0 if x == root else H[x])
            meter.payload['matrixCells'] += 1
            meter.max_nat_cell = max(meter.max_nat_cell, value)
            row.append(value)
        mat.append(tuple(row))
    result = tuple(mat)
    assert result == ref.glue(len(parent), m, v, q, picks)
    return result


def finish(ref, parent, H, m, B, roots, initial, root=0):
    meter = copy.deepcopy(initial)
    for r in roots:
        meter.bump('acceptCalls')
        if all(u == 1 and c <= B for u, c in zip(r.used, r.cost)):
            meter.payload['rootZeroCells'] += m
            return counted_glue(ref, parent, H, m, root, (0,) * m, r.picks, meter, root), meter
    return None, meter


def with_root_guard(parent, H, m, run):
    """Evaluate run only after the dimension check, before any m-vector."""
    mass = sum(H[v] for v in range(1, len(parent)) if parent[v] == 0)
    return run() if m == mass else None


def validate_profile(parent, H, w, m, cert, meter):
    N, n = len(parent), len(parent) - 1
    U = max(H[1:], default=0)
    P = prod(max(1, (int(h == 0) if m == 0 else comb(h + m - 1, m - 1))) for h in H[1:])
    A = sum(meter.raw_by_vertex.values())
    C = int(cert is not None)
    weighted = sum(len([u for u in range(1, N) if parent[u] == v]) * a
                   for v, a in meter.raw_by_vertex.items())
    root_degree = sum(p == 0 for p in parent[1:])
    Y = m * n * (weighted + C * root_degree)
    s, p = meter.key, meter.payload
    assert s['nodeCalls'] == n
    assert all(a <= P for a in meter.raw_by_vertex.values())
    assert A <= n * P and weighted + C * root_degree <= n * P
    assert p['matrices'] == A + C
    assert p['matrixCells'] == m * N * (A + C)
    assert p['columnReads'] == m * (A + C)
    assert p['childReads'] == p['natAdds'] == p['tempCells'] == Y <= m * n * n * P
    assert p['pickCons'] == s['insidePairs'] + s['rootPairs'] <= n * P
    assert p['rootZeroCells'] == m * C
    assert all(L <= P for L in meter.dedup_lengths)
    assert sum(meter.dedup_lengths) == s['dedupInput'] <= 2 * n * P
    assert 2 * p['keyMapCells'] <= sum(L * (L - 1) for L in meter.dedup_lengths)
    assert s['eqCalls'] <= p['keyMapCells'] <= n * P * (P - 1)
    assert meter.max_abs_cost <= sum(abs(z) * h for z, h in zip(w[1:], H[1:]))
    assert meter.max_nat_cell <= U
    payload_bound = (m * N + m + 1) * (n * P + 1) + 3 * m * n * n * P + n * P * P + m
    assert sum(p.values()) <= payload_bound
    logical = sum(s[k] for k in KEY_FIELDS[:15])
    assert logical <= 32 * N * (m + 1) * (U + 1) * P**2
    assert logical + sum(p.values()) <= 64 * (N + 1)**2 * (m + 1) * (U + 1) * P**2


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--baseline', type=Path, default=Path(__file__).with_name('check_subtree_auto_cert.py'))
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('subtree_reference', args.baseline)
    ref = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = ref
    spec.loader.exec_module(ref)
    counts = dict(table_profiles=0, resource_profiles=0, lcm_identities=0,
                  bit_bound_profiles=0, root_guard_checks=0, key_map_gap_checks=0,
                  guard_early_exit_checks=0)
    budgets = [Q(-3, 2), Q(-1, 6), Q(0), Q(1, 2), Q(3), Q(10)]
    for N in range(1, 5):
        for ps in product(*(range(v) for v in range(1, N))):
            parent = (0,) + ps
            fees = [tuple(Q(0) for _ in range(N)), tuple(Q(v + 1, 3) for v in range(N)),
                    tuple(Q((-1)**v * (v + 2), 4) for v in range(N)),
                    tuple(Q(7, 5) if v % 2 else Q(-11, 6) for v in range(N)),
                    tuple(Q(v - 2, 7) for v in range(N))]
            for hs in product(range(3), repeat=N - 1):
                H = (987,) + hs
                for m in range(4):
                    for service in fees:
                        a, D, w = ref.prepare(parent, service)
                        E = lcm(*(x.denominator for x in service[1:]))
                        assert D == E
                        assert D <= prod(x.denominator for x in service[1:])
                        counts['lcm_identities'] += 1
                        ts, rs, initial = counted_tables(ref, parent, H, w, m)
                        expected_tables, expected_roots = ref.run_tables(parent, H, w, m)
                        assert (ts, rs) == (expected_tables, expected_roots)
                        counts['table_profiles'] += 1
                        for T in budgets:
                            DT = D * T
                            B = DT.numerator // DT.denominator
                            cert, meter = finish(ref, parent, H, m, B, rs, initial)
                            assert cert == ref.solve_from_roots(N, m, expected_roots, B)
                            validate_profile(parent, H, w, m, cert, meter)
                            counts['resource_profiles'] += 1
                            b = max([1, abs(T.numerator).bit_length(), T.denominator.bit_length()] +
                                    [t for x in service[1:] for t in
                                     (abs(x.numerator).bit_length(), x.denominator.bit_length())])
                            n, U = N - 1, max(H[1:], default=0)
                            K = (n + 1) * b + 1 + n.bit_length() + U.bit_length()
                            W = sum(abs(z) * h for z, h in zip(w[1:], H[1:]))
                            assert D <= 2**(n*b)
                            assert all(abs(z) < 2**((n+1)*b+1) for z in w)
                            assert abs(B) < 2**((n+1)*b)
                            assert W < 2**K
                            counts['bit_bound_profiles'] += 1
                            root_mass = sum(H[v] for v in ref.children(parent, 0))
                            guarded = cert if m == root_mass else None
                            assert guarded == cert
                            counts['root_guard_checks'] += 1
    probe = Meter()
    xs = [(0, 'old')] * 100 + [(k, 'last') for k in range(20)]
    assert probe.dedup(xs, lambda x: x[0]) == [(k, 'last') for k in range(20)]
    assert probe.payload['keyMapCells'] == 2190 and probe.key['eqCalls'] == 290
    counts['key_map_gap_checks'] += 1

    def forbidden_run():
        raise AssertionError('The mismatched guard evaluated the solver')

    assert with_root_guard((0,), (987,), 2**200, forbidden_run) is None
    counts['guard_early_exit_checks'] += 1
    print(json.dumps({'result': 'PASS', 'scope': 'finite independent source-level resource model',
                      'counts': counts, 'key_map_example': {'cells': 2190, 'comparisons': 290}}, indent=2))


if __name__ == '__main__':
    main()
