"""Finite sanity checks for the proposed paper bounds; NOT a Lean proof.

Python >= 3.10, standard library only. Exhaustive increasing-parent trees of
size <= 4, edge counts 0..2, m=0..3, and four deterministic signed fee patterns.
Direct local-matrix enumeration checks the independently recursive state tables.
All arithmetic is exact. No network, package installation, or timing claims.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, prod, lcm
from collections import Counter


def cols(m, h):
    if m == 0:
        return [()] if h == 0 else []
    return [(a,) + q for a in range(h + 1) for q in cols(m - 1, h - a)]


def calls(m, h):
    return 1 if m == 0 else 1 + sum(calls(m - 1, j) for j in range(h + 1))


def cnum(m, h):
    return int(h == 0) if m == 0 else comb(h + m - 1, m - 1)


def run(parent, H, m, fees, T):
    N = len(parent)
    children = [[u for u in range(1, N) if parent[u] == v] for v in range(N)]
    sub = {}

    def descendants(v):
        sub[v] = [v] + [x for u in children[v] for x in descendants(u)]
        return sub[v]

    descendants(0)
    a = [F(0)] + [fees[x] + (fees[parent[x]] if parent[x] != 0 else 0)
                   for x in range(1, N)]
    D = lcm(*(v.denominator for v in a))
    w = [int(D * v) for v in a]
    stats = Counter()
    tables = {}

    def dedup(xs):
        out = []
        stats['dedupInput'] += len(xs)
        stats['maxRawTable'] = max(stats['maxRawTable'], len(xs))
        for x in reversed(xs):
            for y in out:
                stats['eqCalls'] += 1
                if x == y:
                    break
            else:
                out.insert(0, x)
        stats['dedupOutput'] += len(out)
        stats['maxDedupTable'] = max(stats['maxDedupTable'], len(out))
        return out

    def solve(v):
        stats['nodeCalls'] += 1
        for u in children[v]:
            solve(u)
        rawcols = cols(m, H[v])
        qs = [q for q in rawcols if parent[v] != 0 or max(q, default=0) <= 1]
        stats['compositionCalls'] += calls(m, H[v])
        stats['rangeChoices'] += calls(m, H[v]) - 1
        stats['columnsGenerated'] += len(rawcols)
        stats['columnsAccepted'] += len(qs)
        node_raw = []
        for q in qs:
            A = tuple(t > 0 for t in q)
            acc = [tuple(a[v] * t for t in q)]
            stats['ratMuls'] += m
            stats['maxRawTable'] = max(stats['maxRawTable'], 1)
            stats['maxDedupTable'] = max(stats['maxDedupTable'], 1)
            for u in reversed(children[v]):
                stats['subsetCalls'] += len(tables[u])
                kept = [(B, b) for B, b in tables[u]
                        if all(not B[i] or A[i] for i in range(m))]
                raw = [tuple(b[i] + z[i] for i in range(m))
                       for B, b in kept for z in acc]
                stats['insidePairs'] += len(raw)
                stats['ratAdds'] += m * len(raw)
                acc = dedup(raw)
            node_raw.extend((A, b) for b in acc)
        tables[v] = dedup(node_raw)

    for u in children[0]:
        solve(u)
    root = [(tuple(0 for _ in range(m)), tuple(F(0) for _ in range(m)))]
    stats['maxRawTable'] = max(stats['maxRawTable'], 1)
    stats['maxDedupTable'] = max(stats['maxDedupTable'], 1)
    for u in reversed(children[0]):
        raw = [(tuple(used[i] + int(A[i]) for i in range(m)),
                tuple(z[i] + b[i] for i in range(m)))
               for A, b in tables[u] for used, z in root]
        kept = [(used, z) for used, z in raw if max(used, default=0) <= 1]
        stats['rootPairs'] += len(raw)
        stats['rootRejected'] += len(raw) - len(kept)
        stats['ratAdds'] += m * len(raw)
        stats['maxRawTable'] = max(stats['maxRawTable'], len(raw))
        root = dedup(kept)
    answer = False
    for used, z in root:
        stats['acceptCalls'] += 1
        if all(used[i] == 1 and z[i] <= T for i in range(m)):
            answer = True
            break

    # Direct matrix enumeration: independent of the merge recurrence.
    def matrices(vertices, top):
        for columns in product(*(cols(m, H[x]) for x in vertices)):
            n = dict(zip(vertices, columns))
            if any(n[x][i] > 0 and n[parent[x]][i] == 0
                   for x in vertices if x != top and parent[x] in n for i in range(m)):
                continue
            if top is not None and parent[top] == 0 and max(n[top], default=0) > 1:
                continue
            yield n

    for v, table in tables.items():
        X = sub[v]
        direct = set()
        for n in matrices(X, v):
            A = tuple(n[v][i] > 0 for i in range(m))
            b = tuple(sum((a[x] * n[x][i] for x in X), F(0)) for i in range(m))
            direct.add((A, b))
        assert set(table) == direct
        P_v = prod(max(1, cnum(m, H[x])) for x in X)
        assert len(table) <= P_v
        C = sum(a[x] * H[x] for x in X)
        lo = sum(min(0, w[x] * H[x]) for x in X)
        hi = sum(max(0, w[x] * H[x]) for x in X)
        W = hi - lo
        for A, b in table:
            assert sum(b, F(0)) == C
            assert all(A[i] or b[i] == 0 for i in range(m))
            assert sum(A) <= min(m, H[v])
            assert all((D * z).denominator == 1 and lo <= D * z <= hi for z in b)
        if m >= 1:
            assert len(table) <= 2**m * (W + 1)**(m - 1)
        if H[v] > 0:
            fine = sum(comb(m, r) * (W + 1)**(r - 1)
                       for r in range(1, min(m, H[v]) + 1))
            assert len(table) <= fine
        else:
            assert len(table) == int(all(H[x] == 0 for x in X))
        if parent[v] == 0:
            assert all(sum(A) == H[v] for A, b in table)

    direct_answer = False
    for n in matrices(list(range(1, N)), None):
        if any(sum(n[u][i] for u in children[0]) != 1 for i in range(m)):
            continue
        costs = [sum((a[x] * n[x][i] for x in range(1, N)), F(0)) for i in range(m)]
        if all(b <= T for b in costs):
            direct_answer = True
            # Safe signed completion pruning must preserve this global witness.
            B = (D * T).__floor__()
            for v in range(1, N):
                X = set(sub[v])
                lower_remaining = sum(min(0, w[x] * H[x]) for x in range(1, N) if x not in X)
                for i in range(m):
                    partial = sum(w[x] * n[x][i] for x in X)
                    assert partial + lower_remaining <= B
            break
    assert answer == direct_answer

    P = prod(max(1, cnum(m, H[x])) for x in range(1, N))
    U = max(H[1:], default=0)
    n = N - 1
    assert stats['nodeCalls'] == n
    assert stats['rangeChoices'] + n == stats['compositionCalls']
    assert stats['compositionCalls'] <= n * (m + 1) * (U + 1) * P
    assert stats['columnsGenerated'] <= n * P
    assert stats['columnsAccepted'] <= n * P
    assert stats['subsetCalls'] <= n * P
    assert stats['insidePairs'] + stats['rootPairs'] <= n * P
    assert stats['rootRejected'] <= n * P
    assert stats['ratAdds'] <= m * n * P
    assert stats['ratMuls'] <= m * n * P
    assert stats['dedupInput'] <= 2 * n * P
    assert stats['dedupOutput'] <= 2 * n * P
    assert stats['eqCalls'] <= n * P * P
    assert stats['acceptCalls'] <= P
    assert stats['maxRawTable'] <= P and stats['maxDedupTable'] <= P
    work = sum(v for k, v in stats.items() if not k.startswith('max'))
    assert work <= 32 * N * (m + 1) * (U + 1) * P * P
    return len(tables)


def main():
    for m in range(7):
        for h in range(9):
            qs = cols(m, h)
            assert len(qs) == len(set(qs)) == cnum(m, h)
            assert calls(m, h) == comb(h + m + 1, m)
            assert calls(m, h) <= (m + 1) * (h + 1) * max(1, cnum(m, h))
            if m >= 1:
                assert len(qs) <= m**h
                assert sum(max(q, default=0) <= 1 for q in qs) == (comb(m, h) if h <= m else 0)
    cases = local_tables = 0
    for N in range(1, 5):
        for tail in product(*(range(v) for v in range(1, N))):
            parent = (0,) + tail
            for hs in product(range(3), repeat=N - 1):
                H = (0,) + hs
                for m in range(4):
                    fee_sets = [
                        [F(99)] + [F(0)] * (N - 1),
                        [F(99)] + [F(2)] * (N - 1),
                        [F(99)] + [F(-1 if x % 2 else 2) for x in range(1, N)],
                        [F(99)] + [F((-1)**x * (x + 1), x + 2) for x in range(1, N)],
                    ]
                    for j, fees in enumerate(fee_sets):
                        T = [F(0), F(3), F(-1), F(1, 3)][j]
                        local_tables += run(parent, H, m, fees, T)
                        cases += 1
    print(f'PASS: 63 composition cases; {cases} tree/fee/budget cases; '
          f'{local_tables} local tables matched direct matrices.')
    print('Checked proposed state/grid/raw-list/count bounds and signed pruning necessity.')
    print('Finite Python checks only. No Lean compilation or general proof is claimed.')


if __name__ == '__main__':
    main()
