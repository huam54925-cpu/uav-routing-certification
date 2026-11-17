#!/usr/bin/env python3
"""Independent integer/Fraction replay of H preprocessing and emitted Lean records.

Standard library only. Run outputs belong under ignored verification/runs/.
The optional existing F model checks ordered full certificates for root zero.
This is finite validation of the mathematical model, not a Lean proof or timing.
"""
import argparse
import importlib.util
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import gcd, lcm
from pathlib import Path


def bits(n):
    return abs(n).bit_length()


@dataclass(frozen=True)
class Run:
    value: object
    ops: int
    width: int


def euclid(a, b):
    initial, width, iterations = a, max(bits(a), bits(b)), 0
    while a:
        q, r = divmod(b, a)
        assert 0 <= r < a and r <= b and q <= b
        assert max(bits(q), bits(r), bits(a), bits(b)) <= width
        a, b = r, a
        iterations += 1
    assert iterations <= 2 * bits(initial)
    return Run(b, 4 * iterations + 1, width)


def rat_add(a, b):
    x, y, d = a.numerator * b.denominator, b.numerator * a.denominator, a.denominator * b.denominator
    g = euclid(abs(x + y), d)
    value = Q((x + y) // g.value, d // g.value)
    width = max(max(bits(a.numerator) + bits(b.denominator), bits(b.numerator) + bits(a.denominator)) + 1,
                bits(a.denominator) + bits(b.denominator))
    assert value == a + b
    assert max(bits(x), bits(y), bits(x + y), bits(d), g.width,
               bits(value.numerator), bits(value.denominator)) <= width
    return Run(value, g.ops + 12, width)


def coefficient(parent, root, service, v):
    if v == root:
        return Run(Q(0), 3, max(bits(len(parent)), 1))
    r = rat_add(service[v], Q(0) if parent[v] == root else service[parent[v]])
    return Run(r.value, r.ops + 10, max(bits(len(parent)), r.width))


def collect(rs):
    return Run([r.value for r in rs], sum(r.ops for r in rs) + 2 * len(rs) + 1,
               max([1] + [r.width for r in rs]))


def prepare(parent, root, service, budget):
    n = len(parent)
    cs = collect([coefficient(parent, root, service, v) for v in range(n)])
    d = Run(1, 1, 1)
    prefixes = [1]
    for a in reversed(cs.value):
        g = euclid(a.denominator, d.value)
        raw = a.denominator * d.value
        new_d = raw // g.value
        assert new_d == lcm(a.denominator, d.value)
        width = bits(a.denominator) + bits(d.value)
        assert bits(raw) <= width and bits(new_d) <= width and g.width <= width
        d = Run(new_d, d.ops + g.ops + 6, max(d.width, width))
        prefixes.append(new_d)
    assert all(d.value % x == 0 for x in prefixes)
    ws = []
    for v in range(n):
        a = coefficient(parent, root, service, v)  # Deliberate second evaluation.
        q = d.value // a.value.denominator
        z = q * a.value.numerator
        width = max(bits(d.value) + bits(a.value.numerator), bits(a.value.denominator))
        assert bits(q) <= bits(d.value) and bits(z) <= width
        ws.append(Run(z, a.ops + 4, max(a.width, width)))
    w = collect(ws)
    raw = d.value * budget.numerator
    quotient, remainder = divmod(abs(raw), budget.denominator)
    floor = -quotient - bool(remainder) if raw < 0 else quotient
    assert floor == (d.value * budget).__floor__()
    tw = max(bits(d.value) + bits(budget.numerator) + 1, bits(budget.denominator))
    assert max(bits(raw), bits(quotient + 1), bits(floor), bits(remainder)) <= tw
    expected = [Q(0) if v == root else service[v] + (0 if parent[v] == root else service[parent[v]])
                for v in range(n)]
    assert cs.value == expected
    assert d.value == lcm(*(q.denominator for q in expected))
    assert all(Q(z) == d.value * q for z, q in zip(w.value, expected))
    value = (d.value, w.value, floor)
    return Run(value, cs.ops + d.ops + w.ops + 14, max(cs.width, d.width, w.width, tw))


def root_mass(parent, root, H):
    n, r = len(parent), Run(0, 1, 1)
    total_mass = sum(x for v, x in enumerate(H) if v != root)
    for v in reversed(range(n)):
        if v != root and parent[v] == root:
            r = Run(H[v] + r.value, r.ops + 12, max(bits(n), r.width, bits(H[v]) + bits(r.value) + 1))
        else:
            r = Run(r.value, r.ops + 8, max(bits(n), r.width))
        assert r.value <= total_mass
    return r


def entry(parent, root, H, s, m, T):
    r = root_mass(parent, root, H)
    guard = Run(m == r.value, r.ops + 3, max(r.width, bits(m), bits(r.value)))
    if not guard.value:
        return Run(None, guard.ops + 1, guard.width)
    p = prepare(parent, root, s, T)
    return Run(p.value, guard.ops + p.ops + 2, max(guard.width, p.width))


def load_reference(path):
    import sys
    spec = importlib.util.spec_from_file_location("h_f_reference", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def replay(record, reference):
    parent, root, H, m = record['parent'], record['root'], record['mass'], record['routes']
    s, T = [Q(*q) for q in record['service']], Q(*record['budget'])
    p, r = prepare(parent, root, s, T), root_mass(parent, root, H)
    e = entry(parent, root, H, s, m, T)
    assert list(p.value) == [record['scale'], record['weight'], record['floor']]
    assert [r.value, r.ops, r.width] == record['rootRun']
    assert [p.ops, p.width] == record['prepRun']
    assert [e.ops, e.width] == record['entryRun']
    n = len(parent)
    b = max([1] + [max(bits(q.numerator), bits(q.denominator)) for q in s + [T]])
    h, mu = max(map(bits, H), default=0), bits(m)
    W = (n + 2) * (2*b + h + mu + 4)
    assert e.width <= W and e.ops <= 128*(n+1)*(b+1)
    assert 32*(e.width+1)**2*e.ops <= 4096*(n+1)*(b+1)*(W+1)**2
    assert p.ops <= (48*b+85)*n+17 and p.width <= n+(n+1)*(2*b+2)+b+2
    if m != r.value:
        assert record['certificate'] is None
        assert e.ops <= 12*n+5 and e.width <= n+n*(h+1)+mu+1
        return 'guard'
    if root == 0:
        _, roots = reference.run_tables(parent, H, p.value[1], m)
        cert = reference.solve_from_roots(n, m, roots, p.value[2])
        expected = None if cert is None else [m, [[list(row), 1] for row in cert]]
        assert record['certificate'] == expected
        a = reference.linear_weights(parent, s)
        _, qroots = reference.run_tables(parent, H, a, m)
        assert cert == reference.solve_from_roots(n, m, qroots, T)
        if cert is None:
            return 'none'
        ix = next(i for i, x in enumerate(roots) if all(u == 1 and c <= p.value[2] for u, c in zip(x.used, x.cost)))
        return 'first' if ix == 0 else 'last' if ix + 1 == len(roots) else 'middle'
    return 'nonzero_root'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean-log', type=Path, required=True)
    parser.add_argument('--baseline', type=Path, default=Path(__file__).with_name('check_subtree_auto_cert.py'))
    args = parser.parse_args()
    count = 0
    for a, b in product(range(257), repeat=2):
        assert euclid(a, b).value == gcd(a, b)
        count += 1
    fib = [0, 1]
    for _ in range(400):
        fib.append(fib[-1] + fib[-2])
    for a, b in zip(fib[1:], fib[2:]):
        assert euclid(a, b).value == gcd(a, b)
    rats = sorted({Q(n, d) for n in range(-5, 6) for d in range(1, 10)})
    for a, b in product(rats, repeat=2):
        assert rat_add(a, b).value == a + b
    ref, seen, kinds = load_reference(args.baseline), 0, {}
    for line in args.lean_log.read_text(encoding='utf-8-sig').splitlines():
        if 'HCASE ' not in line:
            continue
        record = json.loads(line.partition('HCASE ')[2])
        kind = replay(record, ref)
        kinds[kind] = kinds.get(kind, 0) + 1
        seen += 1
    assert seen == 608, f'expected 608 Lean records, got {seen}'
    assert all(kinds.get(k, 0) > 0 for k in ['guard', 'none', 'first', 'last', 'nonzero_root'])
    print(json.dumps(dict(status='PASS', euclid_pairs=count, fibonacci_pairs=len(fib)-2,
                          rational_pairs=len(rats)**2, lean_records=seen, certificate_paths=kinds), sort_keys=True))


if __name__ == '__main__':
    main()
