"""Finite falsification checks for the two paper-only excursion lemmas.

No Lean proof, no performance claim, and no unbounded exhaustive claim.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations_with_replacement, permutations, product
import json

COUNTS = Counter()


def visits(w):
    return Counter(v for v in w if v != 'o')


def flow(w):
    return Counter(zip(w, w[1:]))


def fee(w, s):
    return sum((s[v] for v in w if v != 'o'), Q(0))


def add(counters):
    ans = Counter()
    for c in counters:
        ans.update(c)
    return ans


def tree(edges):
    adjacency = {}
    for a, b in edges:
        adjacency.setdefault(a, []).append(b)
        adjacency.setdefault(b, []).append(a)
    return adjacency


def chain(w, adj):
    return all(b in adj[a] for a, b in zip(w, w[1:]))


def legal(w, adj):
    return len(w) >= 3 and w[0] == w[-1] == 'o' and 'o' not in w[1:-1] and chain(w, adj)


def valid_inside(w, inside, adj):
    return bool(w) and w[0] == w[-1] == 'h' and set(w) <= inside and chain(w, adj)


def valid_slot(u, v, inside, adj):
    return (u[0] == 'o' and u[-1] == 'x' and v[0] == 'x' and v[-1] == 'o'
            and 'o' not in u[1:] and 'o' not in v[:-1]
            and not (set(u) | set(v)) & inside and chain(u, adj) and chain(v, adj))


def split(w, inside, adj):
    assert legal(w, adj)
    inward = [i for i, e in enumerate(zip(w, w[1:])) if e == ('x', 'h')]
    outward = [i for i, e in enumerate(zip(w, w[1:])) if e == ('h', 'x')]
    if len(inward) != 1 or len(outward) != 1 or inward[0] >= outward[0]:
        raise ValueError('outside single-excursion domain')
    p, q = inward[0], outward[0]
    u, inner, v = w[:p+1], w[p+1:q+1], w[q+1:]
    assert valid_inside(inner, inside, adj) and valid_slot(u, v, inside, adj)
    assert u + inner + v == w
    return u, inner, v


def internal_walks(inside, adj, max_edges):
    words = []
    def visit(word):
        if word[-1] == 'h':
            words.append(word)
        if len(word) - 1 == max_edges:
            return
        for v in adj[word[-1]]:
            if v in inside:
                visit(word + (v,))
    visit(('h',))
    return words


def signature(words, s):
    return (tuple(sorted(add(visits(w) for w in words).items())),
            tuple(sorted(add(flow(('x',) + w + ('x',)) for w in words).items())),
            tuple(fee(w, s) for w in words))


def check_trees():
    shapes = [
        [('h', 'u'), ('u', 'a')],
        [('h', 'u'), ('h', 'v'), ('u', 'a'), ('u', 'b'), ('v', 'd')],
    ]
    slots = [((('o', 'x', 'c', 'x') if pre else ('o', 'x')),
              (('x', 'c', 'x', 'o') if post else ('x', 'o')))
             for pre, post in product((False, True), repeat=2)]
    budgets = tuple(map(Q, (-4, 0, 3, 7, 13)))
    for edges in shapes:
        inside = set(x for e in edges for x in e)
        adj = tree([('o', 'x'), ('o', 'z'), ('x', 'h'), ('x', 'c')] + edges)
        schedules = [dict.fromkeys(adj, Q(0)),
                     {v: Q((i % 5) - 2, 2) for i, v in enumerate(sorted(adj))},
                     {v: Q((i % 3) + 1) for i, v in enumerate(sorted(adj))}]
        walks = internal_walks(inside, adj, 8)
        COUNTS['internal_walks'] += len(walks)
        for s in schedules:
            groups = {}
            for w in walks:
                sig = signature((w,), s)
                outcomes = []
                for u, v in slots:
                    assert valid_inside(w, inside, adj) and valid_slot(u, v, inside, adj)
                    full = u + w + v
                    assert legal(full, adj)
                    assert split(full, inside, adj) == (u, w, v)
                    assert visits(full) == visits(u) + visits(w) + visits(v)
                    assert flow(full) == flow(u) + flow(('x',) + w + ('x',)) + flow(v)
                    assert fee(full, s) == fee(u, s) + fee(w, s) + fee(v, s)
                    outcomes.extend(fee(full, s) <= b for b in budgets)
                    COUNTS['single_route_identities_and_extractions'] += 1
                if sig in groups:
                    assert groups[sig] == outcomes
                    COUNTS['same_interface_single_witness_comparisons'] += 1
                else:
                    groups[sig] = outcomes

            # First eight walks deliberately include hub-only and deeper visits.
            selected = walks[:8]
            for words in product(selected, repeat=2):
                d_in = add(visits(w) for w in words)
                f_in = add(flow(('x',) + w + ('x',)) for w in words)
                cs = tuple(fee(w, s) for w in words)
                fixed = ('o', 'z', 'o')
                for exterior in product(slots, repeat=2):
                    d_out = add([visits(fixed)] + [visits(p) for uv in exterior for p in uv])
                    f_out = add([flow(fixed)] + [flow(p) for uv in exterior for p in uv])
                    bs = [fee(u, s) + fee(v, s) for u, v in exterior]
                    for allowed in (((0, 1),), ((0, 1), (1, 0)), ()):
                        for bound in budgets:
                            predicted = (fee(fixed, s) <= bound and
                                         any(all(bs[j] + cs[pi[j]] <= bound for j in range(2))
                                             for pi in allowed))
                            actual = False
                            for pi in allowed:
                                routes = [u + words[pi[j]] + v for j, (u, v) in enumerate(exterior)] + [fixed]
                                assert all(legal(r, adj) for r in routes)
                                assert add(visits(r) for r in routes) == d_in + d_out
                                assert add(flow(r) for r in routes) == f_in + f_out
                                actual |= all(fee(r, s) <= bound for r in routes)
                            assert actual == predicted
                            COUNTS['family_gluing_iff_comparisons'] += 1
        repeated = ('o', 'x', 'h', 'x', 'h', 'x', 'o')
        assert legal(repeated, adj)
        try:
            split(repeated, inside, adj)
            raise AssertionError('accepted repeated separator crossing')
        except ValueError:
            COUNTS['double_entry_rejections'] += 1
        COUNTS['nonstar_internal_shapes'] += 1
    # Leaf multiplicity cannot determine h-count by the old star formula.
    w = ('h', 'u', 'a', 'u', 'a', 'u', 'h')
    assert visits(w) == Counter(h=2, u=3, a=2)
    assert visits(w)['h'] != 1 + visits(w)['a']


def check_matching():
    values = (Q(-2), Q(-1, 2), Q(0), Q(3, 2))
    for k in range(5):
        lists = tuple(combinations_with_replacement(values, k))
        perms = tuple(permutations(range(k)))
        for b_asc, c in product(lists, repeat=2):
            b = b_asc[::-1]
            all_costs = [tuple(b[j] + c[pi[j]] for j in range(k)) for pi in perms]
            if k:
                sorted_max = max(b[j] + c[j] for j in range(k))
                optimal_max = min(max(costs) for costs in all_costs)
                assert sorted_max == optimal_max
                # Also test the stronger prefix/pigeonhole step per permutation.
                for pi in perms:
                    for j in range(k):
                        witnesses = [i for i in range(j+1) if pi[i] >= j]
                        assert witnesses
                        assert any(b[j] + c[j] <= b[i] + c[pi[i]] for i in witnesses)
                        COUNTS['prefix_pigeonhole_checks'] += 1
                breaks = sorted(set(x for costs in all_costs for x in costs))
                thresholds = sorted(set(breaks + [x - Q(1, 4) for x in breaks] + [breaks[-1] + 1]))
                COUNTS['minimax_equalities'] += 1
            else:
                thresholds = [Q(-7), Q(0), Q(7)]
            for bound in thresholds:
                exists = any(all(x <= bound for x in costs) for costs in all_costs)
                ordered = all(b[j] + c[j] <= bound for j in range(k))
                assert exists == ordered
                COUNTS['sorted_budget_iff_cases'] += 1
            COUNTS['sorted_vector_pairs'] += 1
    # A fixed policy need not contain the freely optimal matching.
    b, c, bound = (Q(6), Q(0)), (Q(2), Q(1)), Q(7)
    assert not all(b[j] + c[j] <= bound for j in range(2))
    assert all(b[j] + sorted(c)[j] <= bound for j in range(2))
    assert Q(-4) + Q(10) <= Q(7)


def main():
    if not __debug__:
        raise RuntimeError('Run without -O: assertions are required for these checks.')
    COUNTS.clear()
    check_trees()
    check_matching()
    report = dict(status='PASS', counts=dict(COUNTS),
                  scope=dict(internal_shapes='path h-u-a; branching h-u,h-v,u-a,u-b,v-d',
                             max_internal_edges=8, fee_schedules=3, exterior_slots=4,
                             family_walk_sample='first 8 generated walks per shape',
                             matching_k='0..4', matching_values=['-2','-1/2','0','3/2']),
                  limitations=['Finite Python tests, not Lean proof or unbounded verification.',
                               'No arbitrary-summary realizability or recursive-state completeness claim.'])
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
