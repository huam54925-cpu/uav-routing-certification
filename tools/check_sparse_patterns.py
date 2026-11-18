"""Independent finite checks for the A0--A2 sparse-pattern theorems.

Uses visit costs, rather than the linearized cost, as the reference semantics.
This finite test is a regression check, not a substitute for the Lean proof.
Run from the repository root: python tools/check_sparse_patterns.py
"""

from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import prod


def old_valid(parent, root, cap, fees, budget, row):
    n = len(parent)
    children = [[v for v in range(n) if v != root and parent[v] == u]
                for u in range(n)]
    visits = [0 if v == root else row[v] + sum(row[w] for w in children[v])
              for v in range(n)]
    return (row[root] == 0
            and all(row[v] <= cap[v] for v in range(n) if v != root)
            and sum(row[v] for v in children[root]) == 1
            and all(not row[v] or row[parent[v]]
                    for v in range(n) if v != root and parent[v] != root)
            and sum(fees[v] * visits[v] for v in range(n)) <= budget)


def linear_valid(parent, root, cap, fees, budget, row):
    return (row[root] == 0
            and all(row[v] <= cap[v] for v in range(len(parent)) if v != root)
            and sum(row[v] for v in range(len(parent))
                    if v != root and parent[v] == root) == 1
            and all(row[v] <= cap[v] * row[parent[v]]
                    for v in range(len(parent)) if v != root and parent[v] != root)
            and sum((fees[v] + (0 if parent[v] == root else fees[parent[v]])) * row[v]
                    for v in range(len(parent)) if v != root) <= budget)


def run():
    instances = rows_checked = midpoints = feasible = exchanges = 0
    trees = [((0,), 0), ((0, 0, 1), 0), ((1, 2, 2), 2),
             ((0, 0, 1, 1), 0), ((0, 0, 0, 0), 0)]
    for parent, root in trees:
        n = len(parent)
        nonroot = [v for v in range(n) if v != root]
        fee_vectors = [tuple(Fraction(a) for _ in parent) for a in (-1, 0, 1)]
        fee_vectors.append(tuple(Fraction((-1) ** v * (v + 1), v + 2) for v in range(n)))
        for caps in product(range(4), repeat=n - 1):
            cap = [0] * n
            for v, c in zip(nonroot, caps):
                cap[v] = c
            m = sum(cap[v] for v in nonroot if parent[v] == root)
            all_rows = list(product(*(range(c + 1) for c in cap)))
            for fees, budget in product(fee_vectors, map(Fraction, (-6, -1, 0, 2, 6))):
                instances += 1
                patterns = []
                for row in all_rows:
                    rows_checked += 1
                    valid = old_valid(parent, root, cap, fees, budget, row)
                    assert valid == linear_valid(parent, root, cap, fees, budget, row)
                    if valid:
                        patterns.append(row)
                for p, q in combinations(patterns, 2):
                    if all((a - b) % 2 == 0 for a, b in zip(p, q)):
                        r = tuple((a + b) // 2 for a, b in zip(p, q))
                        assert old_valid(parent, root, cap, fees, budget, r)
                        assert 2 * sum(x*x for x in r) < sum(x*x for x in p + q)
                        midpoints += 1
                representations = []
                # Only small regression instances are expanded in this independent
                # test. The Lean checker and future binary checker do not expand m.
                for ids in combinations_with_replacement(range(len(patterns)), m):
                    if all(sum(patterns[i][v] for i in ids) == cap[v] for v in nonroot):
                        representations.append(tuple(ids.count(i) for i in range(len(patterns))))
                if not representations:
                    continue
                feasible += 1
                z = min(representations, key=lambda z: sum(c > 0 for c in z))
                support = [i for i, c in enumerate(z) if c]
                k = len(support)
                assert 2 ** k <= (m + 1) * prod(c + 1 for c in caps)
                assert k <= m.bit_length() + sum(c.bit_length() for c in caps)
                assert k <= 2 ** (n - 1)
                sums = set()
                for mask in product((False, True), repeat=k):
                    chosen = [i for i, yes in zip(support, mask) if yes]
                    value = (len(chosen), *(sum(patterns[i][v] for i in chosen) for v in nonroot))
                    assert value not in sums
                    sums.add(value)
                ze = min(representations, key=lambda z: sum(c * sum(x*x for x in p)
                         for c, p in zip(z, patterns)))
                parities = [tuple(x % 2 for x in p) for c, p in zip(ze, patterns) if c]
                assert len(parities) == len(set(parities))

    # A genuine equal-subset-sum exchange with unequal multiplicities.
    atoms = [(1, 0), (1, 1), (1, 2), (1, 3)]
    z = [2, 1, 1, 3]
    left, right = [0, 3], [1, 2]
    delta = min(z[i] for i in left)
    zp = [c - (delta if i in left else 0) + (delta if i in right else 0)
          for i, c in enumerate(z)]
    assert all(sum(c * a[v] for c, a in zip(z, atoms)) ==
               sum(c * a[v] for c, a in zip(zp, atoms)) for v in range(2))
    assert sum(c > 0 for c in zp) < sum(c > 0 for c in z)
    exchanges += 1

    # The parent/child guard is not child <= parent; zero parent blocks a child.
    assert old_valid((0, 0, 1), 0, (0, 1, 3), (0, 0, 0), 0, (0, 1, 3))
    assert not old_valid((0, 0, 1), 0, (0, 0, 3), (0, 0, 0), 0, (0, 0, 3))

    # The first support-minimal witness need not minimize squared energy.
    # Two routes with child total 3 cannot use a single integral pattern.
    choices = [(1, 0, 0, 1), (0, 1, 1, 0)]
    support_min = min(choices, key=lambda z: sum(c > 0 for c in z))
    energy_min = min(choices, key=lambda z: sum(c * (i*i + 1) for i, c in enumerate(z)))
    assert support_min != energy_min
    assert sum(c > 0 for c in support_min) == sum(c > 0 for c in energy_min) == 2
    print(f"PASS: {instances} instances; {rows_checked} rows; {midpoints} midpoint pairs; "
          f"{feasible} feasible instances; {exchanges} multiplicity exchange; distinct minimizers")


if __name__ == "__main__":
    run()
