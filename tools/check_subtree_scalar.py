#!/usr/bin/env python3
"""Independent I reference execution and exact scalar-counter replay.

Only Python's standard library is used. The meter charges loop bodies as they
execute; it does not compute the DP count from G's final resource bound. Raw
records belong in ignored verification/runs/. This is not a timing benchmark.
"""
import argparse
import importlib.util
import json
import sys
from fractions import Fraction
from pathlib import Path


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


class Scalar:
    def __init__(self):
        self.ops = 0
        self.width = 0
        self.max_length = 0
        self.eq_coordinates = []

    def pay(self, n, *values):
        self.ops += n
        self.width = max([self.width] + [abs(int(v)).bit_length() for v in values])

    def sequence(self, xs):
        self.max_length = max(self.max_length, len(xs))
        return xs

    def enumeration(self, n, tariff=2):
        for i in range(n):
            self.pay(tariff, i, i + 1, n)
        self.pay(1, n)
        return self.sequence(list(range(n)))

    def mapping(self, f, xs):
        out = []
        for x in xs:
            out.append(f(x))
            self.pay(3)
        self.pay(1)
        return self.sequence(out)

    def filtering(self, p, xs):
        out = []
        for x in xs:
            if p(x):
                out.append(x)
            self.pay(4)
        self.pay(1)
        return self.sequence(out)

    def flat_mapping(self, f, xs):
        out = []
        for x in xs:
            ys = f(x)
            for y in ys:
                self.pay(3)
                out.append(y)
            self.pay(4)  # append terminal, outer continuation
        self.pay(1)
        return self.sequence(out)

    def all(self, p, xs):
        for x in xs:
            b = p(x)
            self.pay(3)
            if not b:
                return False
        self.pay(1)
        return True

    def vector(self, f, n):
        out = []
        for i in range(n):
            out.append(f(i))
            self.pay(5, i, i + 1, n)
        self.pay(1)
        return tuple(self.sequence(out))

    def eq(self, x, y):
        checks = 0

        def coordinate(i):
            nonlocal checks
            checks += 1
            self.pay(3, x[i], y[i])
            return x[i] == y[i]

        result = self.all(coordinate, self.enumeration(len(x)))
        self.eq_coordinates.append(checks)
        return result

    def fields(self, x, y):
        k = self.eq(x[0], y[0])
        self.pay(1)
        return self.eq(x[1], y[1]) if k else False

    def dedup(self, xs, key, eq):
        out = []
        self.pay(1)
        for x in reversed(xs):
            def project(y):
                self.pay(1)
                return key(y)
            keys = self.mapping(project, out)
            found = False
            for k in keys:
                found = eq(key(x), k)
                self.pay(4)
                if found:
                    break
            if not found:
                self.pay(1)  # exhausted membership, including the empty scan
                out = [x] + out
            self.pay(7)
        self.pay(2)
        return self.sequence(out)

    def solve(self, ref, parent, H, w, m, B, root=0):
        n = len(parent)
        tables = {}

        def children(v):
            def p(u):
                self.pay(6, root, parent[u], v, u)
                return u != root and parent[u] == v
            return self.filtering(p, self.enumeration(n))

        def compositions(d, h):
            self.pay(0, d, h)
            if d == 0:
                self.pay(4)
                return [()] if h == 0 else []
            runs = []
            for a in range(h + 1):
                tails = compositions(d - 1, h - a)
                def cons(t):
                    return self.vector(lambda i: read((a,) + t, i, 3), d)
                runs.append(self.mapping(cons, tails))
                self.pay(1, a, h - a)
            def identity(xs):
                self.pay(1)
                return xs
            out = self.flat_mapping(identity, runs)
            self.pay(6 * (h + 1) + 4, h + 1)
            return out

        def read(xs, i, cost):
            self.pay(cost, xs[i])
            return xs[i]

        def support(q):
            return self.vector(lambda i: positive(q[i]), m)

        def positive(x):
            self.pay(2, x)
            return x > 0

        def add(x, y):
            def cell(i):
                z = x[i] + y[i]
                self.pay(3, x[i], y[i], z)
                return z
            return self.vector(cell, m)

        def subset(a, b):
            def p(i):
                self.pay(4, a[i], b[i])
                return not a[i] or b[i]
            return self.all(p, self.enumeration(m))

        def inside(a, base, ts):
            if not ts:
                self.pay(4)
                return [(base, ())]
            rest = inside(a, base, ts[1:])
            def eligible(e):
                z = subset(e.active, a)
                self.pay(1)
                return z
            good = self.filtering(eligible, ts[0])
            def pairs(e):
                def pair(r):
                    c = add(e.cost, r[0])
                    self.pay(5)
                    return (c, (e,) + r[1])
                return self.mapping(pair, rest)
            raw = self.flat_mapping(pairs, good)
            out = self.dedup(raw, lambda r: r[0], self.eq)
            self.pay(5)
            return out

        def glue(v, q, picks):
            def row(i):
                def cell(x):
                    if x == v:
                        self.pay(2, q[i])
                        return q[i]
                    temp = self.mapping(lambda e: read(e.matrix[i], x, 3), picks)
                    total = 0
                    self.pay(1)
                    for a in reversed(temp):
                        self.pay(4, a, total, a + total)
                        total += a
                    self.pay(1)
                    return total
                return self.vector(cell, n)
            return self.vector(row, m)

        def candidate_cap(v, q):
            self.pay(0, parent[v], root)
            if parent[v] != root:
                self.pay(3)
                return True
            def p(i):
                self.pay(2, q[i])
                return q[i] <= 1
            self.pay(3)  # enumeration supplies the remaining terminal instruction
            return self.all(p, self.enumeration(m))

        def node(v, ts):
            qs = self.filtering(lambda q: candidate_cap(v, q), compositions(m, H[v]))
            self.pay(3, H[v], w[v])
            runs = []
            for q in qs:
                a = support(q)
                def scale(i):
                    z = w[v] * q[i]
                    self.pay(4, w[v], q[i], z)
                    return z
                base = self.vector(scale, m)
                r = inside(a, base, ts)
                def entry(b):
                    a2 = support(q)
                    g = glue(v, q, b[1])
                    self.pay(5)
                    return ref.Entry(a2, b[0], g)
                runs.append(self.mapping(entry, r))
                self.pay(4)
            self.pay(3 * len(runs) + 1)
            def identity(xs):
                self.pay(1)
                return xs
            raw = self.flat_mapping(identity, runs)
            result = self.dedup(raw, lambda e: (e.active, e.cost), self.fields)
            self.pay(5)
            return result

        def compute(v):
            ch = children(v)
            ts = [compute(u) for u in ch]
            self.pay(3 * len(ch) + 1)
            result = node(v, ts)
            self.pay(5)
            tables[v] = result
            return result

        def zero(_):
            self.pay(1, 0)
            return 0

        def roots(ts):
            if not ts:
                z, c = self.vector(zero, m), self.vector(zero, m)
                self.pay(5)
                return [ref.Root(z, c, ())]
            rest = roots(ts[1:])
            def pairs(e):
                def pair(r):
                    def used(i):
                        z = r.used[i] + int(e.active[i])
                        self.pay(4, r.used[i], int(e.active[i]), z)
                        return z
                    u, c = self.vector(used, m), add(r.cost, e.cost)
                    self.pay(7)
                    return ref.Root(u, c, (e,) + r.picks)
                return self.mapping(pair, rest)
            raw = self.flat_mapping(pairs, ts[0])
            def cap(r):
                def p(i):
                    self.pay(2, r.used[i])
                    return r.used[i] <= 1
                z = self.all(p, self.enumeration(m))
                self.pay(1)
                return z
            kept = self.filtering(cap, raw)
            result = self.dedup(kept, lambda r: (r.used, r.cost), self.fields)
            self.pay(5)
            return result

        ch = children(root)
        ts = [compute(v) for v in ch]
        self.pay(3 * len(ch) + 1)
        rs = roots(ts)
        selected = None
        for r in rs:
            def p(i):
                self.pay(5, r.used[i], r.cost[i], B)
                return r.used[i] == 1 and r.cost[i] <= B
            accepted = self.all(p, self.enumeration(m))
            self.pay(5)
            if accepted:
                selected = r
                break
        if selected is None:
            self.pay(3)  # exhausted find and none finish
            cert = None
        else:
            cert = glue(root, self.vector(zero, m), selected.picks)
            self.pay(6)
        self.pay(7)
        return cert, tables, rs


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean-log', type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).parent
    ref = load('scalar_f_ref', here / 'check_subtree_auto_cert.py')
    old = load('scalar_g_ref', here / 'check_subtree_resources.py')
    pre = load('scalar_h_ref', here / 'check_subtree_preprocessing.py')
    records = []
    log = args.lean_log.read_text(encoding='utf-8-sig')
    assert "error:" not in log and "error(" not in log, "Lean log contains errors"
    assert "PASS I Lean: 608 complete records" in log, "Lean replay did not finish"
    for line in log.splitlines():
        if line.startswith('ICASE '):
            records.append(json.loads(line[6:]))
    assert len(records) == 608, 'Expected the complete 608-record replay'
    passed = rejected = 0
    for row in records:
        parent, H, m, root = row['parent'], row['mass'], row['routes'], row['root']
        service = [Fraction(*q) for q in row['service']]
        T = Fraction(*row['budget'])
        g = pre.root_mass(parent, root, H)
        guard_width = max(g.width, m.bit_length(), g.value.bit_length())
        if m != g.value:
            assert row['entryRun'] == [g.ops + 4, guard_width]
            assert row['certificate'] is None
            assert row['keyStats'] == [0]*17 and row['payload'] == [0]*9
            rejected += 1
            continue
        p = pre.prepare(parent, root, service, T)
        D, w, B = p.value
        meter = Scalar()
        cert, tables, roots = meter.solve(ref, parent, H, w, m, B, root)
        assert meter.ops == row['dpOps'], (row, meter.ops)
        assert row['entryRun'][0] == g.ops + 3 + p.ops + meter.ops + 8
        b = max([1, abs(T.numerator).bit_length(), T.denominator.bit_length()] +
                [z for q in service for z in (abs(q.numerator).bit_length(), q.denominator.bit_length())])
        h = max([0] + [v.bit_length() for v in H])
        width = (len(parent)+2)*(b+h+2)+len(parent)+m+meter.ops+4
        assert row['entryRun'][1] == max(guard_width, p.width, width)
        assert meter.width + 1 <= width and meter.max_length.bit_length() + 1 <= width
        observed = None if cert is None else [m, [[list(r), 1] for r in cert]]
        assert observed == row['certificate']
        old_tables, old_roots, gm = old.counted_tables(ref, parent, H, w, m, root)
        old_cert, gm = old.finish(ref, parent, H, m, B, old_roots, gm, root)
        assert cert == old_cert and tables == old_tables and roots == old_roots
        assert row['keyStats'] == [gm.key[k] for k in old.KEY_FIELDS]
        assert row['payload'] == [gm.payload[k] for k in old.PAYLOAD_FIELDS]
        resource = sum(gm.key[k] for k in old.KEY_FIELDS[:15]) + sum(gm.payload.values())
        assert meter.ops <= 4096*(len(parent)+1)*(m+1)**2*(1+resource)
        passed += 1
    boundary = 0
    for n in range(49):
        x = tuple(range(n))
        for pos in range(n + 1):
            y = tuple(v + int(i == pos) for i, v in enumerate(x))
            meter = Scalar()
            equal = meter.eq(x, y)
            checks = n if pos == n else pos + 1
            assert equal == (x == y)
            assert meter.ops == 2*n+1+6*checks+int(equal)
            boundary += 1
    print(f'PASS I Python: {len(records)} full records ({passed} passing, {rejected} guard rejects); '
          f'{boundary} coordinate-prefix boundaries; exact counters, all G fields and ranges')


if __name__ == '__main__':
    main()
