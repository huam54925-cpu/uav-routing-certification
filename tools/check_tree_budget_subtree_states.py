"""Bounded subtree-state regression against independent matrix enumeration.

Adapted from the user-supplied issue19_today_plan_proofs_20261113_zh.tex.
Uses exact integer arithmetic; does not measure algorithmic complexity.
Run from the repository root: python tools/check_tree_budget_subtree_states.py
"""
from itertools import product


def compositions(total, m):
    if m == 0:
        return [()] if total == 0 else []
    if m == 1:
        return [(total,)]
    return [(a,) + rest for a in range(total + 1)
            for rest in compositions(total - a, m - 1)]


def check(parent, h, fee, m):
    n = len(parent)
    children = [[v for v in range(1, n) if parent[v] == u]
                for u in range(n)]
    nodes = [[] for _ in range(n)]
    for v in reversed(range(n)):
        nodes[v] = [v] + [x for u in children[v] for x in nodes[u]]
    choices = [compositions(h[v], m) for v in range(n)]
    exact, compact = {}, {}
    for v in reversed(range(1, n)):
        table, small = set(), set()
        for q in choices[v]:
            for sub in product(*(exact[u] for u in children[v])):
                if any(qc[i] > 0 and q[i] == 0
                       for qc, cc in sub for i in range(m)):
                    continue
                c = tuple(fee[v] * (q[i] + sum(qc[i] for qc, cc in sub))
                          + sum(cc[i] for qc, cc in sub) for i in range(m))
                table.add((q, c))
            if parent[v] == 0 and any(x > 1 for x in q):
                continue
            support = frozenset(i for i in range(m) if q[i] > 0)
            weight = fee[v] + (fee[parent[v]] if parent[v] != 0 else 0)
            for sub in product(*(compact[u] for u in children[v])):
                if any(not a <= support for a, b in sub):
                    continue
                b = tuple(weight * q[i] + sum(bc[i] for a, bc in sub)
                          for i in range(m))
                small.add((support, b))
        brute, brute_small = set(), set()
        for cols in product(*(choices[u] for u in nodes[v])):
            a = dict(zip(nodes[v], cols))
            if any(a[u][i] > 0 and a[parent[u]][i] == 0
                   for u in nodes[v] if u != v for i in range(m)):
                continue
            q = a[v]
            c = tuple(sum(fee[u] * (a[u][i] + sum(a[w][i] for w in children[u]))
                          for u in nodes[v]) for i in range(m))
            brute.add((q, c))
            if parent[v] != 0 or all(x <= 1 for x in q):
                b = tuple(c[i] + (fee[parent[v]] * q[i] if parent[v] != 0 else 0)
                          for i in range(m))
                brute_small.add((frozenset(i for i in range(m) if q[i]), b))
        assert table == brute, (parent, h, fee, m, v, 'full')
        assert small == brute_small, (parent, h, fee, m, v, 'compact')
        exact[v], compact[v] = table, small
    direct_costs = set()
    for cols in product(*(choices[v] for v in range(1, n))):
        a = {v: cols[v - 1] for v in range(1, n)}
        if any(sum(a[v][i] for v in children[0]) != 1 for i in range(m)):
            continue
        if any(a[v][i] > 0 and a[parent[v]][i] == 0
               for v in range(1, n) if parent[v] != 0 for i in range(m)):
            continue
        direct_costs.add(tuple(sum(fee[v] * (a[v][i] + sum(a[u][i] for u in children[v]))
                                  for v in range(1, n)) for i in range(m)))
    full_root_costs = set()
    for sub in product(*(exact[v] for v in children[0])):
        if any(sum(q[i] for q, c in sub) != 1 for i in range(m)):
            continue
        full_root_costs.add(tuple(sum(c[i] for q, c in sub) for i in range(m)))
    assert full_root_costs == direct_costs, (parent, h, fee, m, 'full root')
    root_costs = set()
    for sub in product(*(compact[v] for v in children[0])):
        if any(sum(i in a for a, b in sub) != 1 for i in range(m)):
            continue
        root_costs.add(tuple(sum(b[i] for a, b in sub) for i in range(m)))
    assert root_costs == direct_costs, (parent, h, fee, m, 'root')


if __name__ == '__main__':
    cases = 0
    for n in range(1, 5):
        for tail in product(*(range(v) for v in range(1, n))):
            parent = (0,) + tail
            for htail in product(range(3), repeat=n - 1):
                for stail in product((-1, 2), repeat=n - 1):
                    for m in range(4):
                        check(parent, (0,) + htail, (99,) + stail, m)
                        cases += 1
    print(f'PASS: {cases} exhaustive parameter configurations; all subtree state sets and root cost sets agree.')
