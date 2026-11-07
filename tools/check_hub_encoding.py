"""Independent finite reference tests for the Issue 23 binary encoding note.

This is a Python model, not Lean verification or a machine-time proof.
Uses only the Python standard library; results go to stdout, with no file writes.
The bitstring format is sparse: parent/H records, demand, then service.
Malformed length headers are checked against already-parsed tokens before
any header-sized range, allocation, or certificate parsing.
"""
from collections import Counter
from dataclasses import dataclass
from itertools import product
import json
import platform
import random


class InvalidCode(ValueError):
    pass


COUNTS = Counter()
REGRESSIONS = []


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def ell(n):
    if not isinstance(n, int) or n < 0:
        raise InvalidCode('natural required')
    return 2 * (n + 1).bit_length() - 1


def g(n):
    ell(n)
    payload = bin(n + 1)[2:]
    return '0' * (len(payload) - 1) + payload


def read_nat(bits, pos):
    """Read one self-delimiting code; work is bounded by the supplied suffix."""
    begin = pos
    while pos < len(bits) and bits[pos] == '0':
        pos += 1
    if pos == len(bits) or bits[pos] != '1':
        raise InvalidCode('missing leading one')
    zeros = pos - begin
    end = pos + zeros + 1
    if end > len(bits):
        raise InvalidCode('truncated payload')
    payload = bits[pos:end]
    if any(c not in '01' for c in payload):
        raise InvalidCode('non-binary payload')
    return int(payload, 2) - 1, end


def decode_stream(bits):
    if not isinstance(bits, str):
        raise InvalidCode('bitstring required')
    pos, values = 0, []
    while pos < len(bits):
        n, pos = read_nat(bits, pos)
        values.append(n)
    return tuple(values)


@dataclass(frozen=True)
class Source:
    m: int
    budget: int
    weights: tuple


def encode_source(source):
    if len(source.weights) != 3 * source.m:
        raise InvalidCode('item count')
    return ''.join(g(x) for x in (source.m, source.budget, *source.weights))


def decode_source(bits):
    # Parse supplied tokens to EOF first, never loop 3*m times from a header.
    xs = decode_stream(bits)
    if len(xs) < 2:
        raise InvalidCode('source headers')
    m, budget = xs[:2]
    if len(xs) - 2 != 3 * m:
        raise InvalidCode('source item count')
    return Source(m, budget, xs[2:])


def valid_source(source):
    return (len(source.weights) == 3 * source.m and source.budget > 0
            and all(source.budget < 4 * a and 2 * a < source.budget
                    for a in source.weights)
            and sum(source.weights) == source.m * source.budget)


@dataclass(frozen=True)
class Target:
    vertices: int
    m: int
    budget: int
    parents: tuple
    multiplicities: tuple
    demands: tuple
    fees: tuple


def encode_target(target):
    n = target.vertices
    if (n < 1 or len(target.parents) != n - 1 or len(target.multiplicities) != n - 1
            or len(target.demands) != n or len(target.fees) != n):
        raise InvalidCode('target lengths')
    if any(not 0 <= p < v for v, p in enumerate(target.parents, start=1)):
        raise InvalidCode('parent order')
    values = [n, target.m, target.budget]
    for p, h in zip(target.parents, target.multiplicities):
        values.extend((p, h))
    values.extend(target.demands)
    values.extend(target.fees)
    return ''.join(g(x) for x in values)


def decode_target(bits):
    xs = decode_stream(bits)
    if len(xs) < 3:
        raise InvalidCode('target headers')
    n, m, budget = xs[:3]
    if n < 1 or len(xs) - 3 != 4 * n - 2:
        raise InvalidCode('target payload count')
    # n is now bounded by the actual decoded payload.
    end_pairs = 3 + 2 * (n - 1)
    pairs = xs[3:end_pairs]
    parents, mult = pairs[0::2], pairs[1::2]
    if any(p >= v for v, p in enumerate(parents, start=1)):
        raise InvalidCode('parent order')
    return Target(n, m, budget, parents, mult,
                  xs[end_pairs:end_pairs+n], xs[end_pairs+n:])


def canonical_target(source):
    # This constructor requires structural source decoding, not validity.
    q = len(source.weights)
    if q != 3 * source.m:
        raise InvalidCode('source length')
    return Target(q + 2, source.m, source.budget,
                  (0,) + (1,) * q, (source.m,) + (1,) * q,
                  (0, 4 * source.m) + (1,) * q,
                  (0, 0) + source.weights)


def has_h0_shape(target):
    """Check canonical format only, without deciding routing feasibility."""
    n, m = target.vertices, target.m
    if (n != 3 * m + 2 or len(target.parents) != n - 1
            or len(target.multiplicities) != n - 1
            or len(target.demands) != n or len(target.fees) != n):
        return False
    # Each size is bounded by tuples supplied in the decoded target.
    return (target.parents[0] == 0 and all(x == 1 for x in target.parents[1:])
            and target.multiplicities[0] == m
            and all(x == 1 for x in target.multiplicities[1:])
            and target.demands[:2] == (0, 4 * m)
            and all(x == 1 for x in target.demands[2:])
            and target.fees[:2] == (0, 0))


NO_SOURCE = Source(2, 30, (9, 9, 9, 13, 10, 10))
NO_TARGET = canonical_target(NO_SOURCE)
NO_BITS = encode_target(NO_TARGET)


def reduce_bits(bits):
    try:
        source = decode_source(bits)
    except InvalidCode:
        return NO_BITS
    if not valid_source(source):
        return NO_BITS
    return encode_target(canonical_target(source))


def certificate_width(m):
    return max(1, m.bit_length())


def encode_certificate(labels, m):
    if len(labels) != 3 * m or any(not 0 <= r < m for r in labels):
        raise InvalidCode('certificate labels')
    width = certificate_width(m)
    return ''.join(format(r, f'0{width}b') for r in labels)


def check_certificate(target_bits, certificate_bits):
    try:
        target = decode_target(target_bits)
    except InvalidCode:
        return False
    if not has_h0_shape(target) or not isinstance(certificate_bits, str):
        return False
    m, q = target.m, len(target.fees) - 2
    width = certificate_width(m)
    if len(certificate_bits) != q * width or any(c not in '01' for c in certificate_bits):
        return False
    # m <= vertices <= supplied tuple/bitstring size by the checks above.
    loads = [0] * m
    for i in range(q):
        label = int(certificate_bits[i*width:(i+1)*width], 2)
        if label >= m:
            return False
        loads[label] += target.fees[i+2]
    return all(load <= target.budget for load in loads)


def assignment_loads(weights, labels, m):
    loads, sizes = [0] * m, [0] * m
    for a, label in zip(weights, labels):
        loads[label] += a
        sizes[label] += 1
    return loads, sizes


def is_three_partition(source, labels):
    loads, sizes = assignment_loads(source.weights, labels, source.m)
    return all(w == source.budget and size == 3 for w, size in zip(loads, sizes))


def reconstruct_routes(target, labels):
    require(has_h0_shape(target), 'reconstruction domain')
    require(len(labels) == len(target.fees) - 2 and all(0 <= r < target.m for r in labels),
            'reconstruction labels')
    routes = []
    for r in range(target.m):
        route = [0, 1]
        for i, label in enumerate(labels):
            if label == r:
                route.extend((i+2, 1))
        route.append(0)
        routes.append(tuple(route))
    return routes


def validate_routes(target, labels):
    routes = reconstruct_routes(target, labels)
    actual_d, actual_f = Counter(), Counter()
    expected_f = Counter()
    for v, (p, h) in enumerate(zip(target.parents, target.multiplicities), start=1):
        if h:
            expected_f[(p, v)] = h
            expected_f[(v, p)] = h
    costs = []
    for route in routes:
        require(len(route) >= 3 and route[0] == route[-1] == 0
                and 0 not in route[1:-1], 'original-depot legality')
        for u, v in zip(route, route[1:]):
            require(u != v and (target.parents[max(u, v)-1] == min(u, v)), 'tree edge')
        actual_d.update(route[1:-1])
        actual_f.update(zip(route, route[1:]))
        costs.append(sum(target.fees[v] for v in route[1:-1]))
    require(all(actual_d[v] == target.demands[v] for v in range(1, target.vertices)),
            'exact visits')
    require(actual_f == expected_f, 'exact parent-edge flow')
    require(costs == assignment_loads(target.fees[2:], labels, target.m)[0], 'exact row cost')
    COUNTS['list_reconstruction_cases'] += 1
    return all(c <= target.budget for c in costs)


def assert_rejected_source(bits):
    require(reduce_bits(bits) == NO_BITS, 'invalid input did not map to fixed NO')
    require(len(reduce_bits(bits)) <= 4 * len(bits) + 129, 'total reduction length')
    COUNTS['invalid_source_reductions'] += 1


def integer_tests():
    values = list(range(4097))
    for k in range(1, 257):
        values.extend((2**k - 2, 2**k - 1, 2**k, 2**k + 1))
    values.extend((2**4096 - 1, 2**4096, 2**4096 + 1))
    for n in values:
        encoded = g(n)
        require(len(encoded) == ell(n), 'integer length')
        require(decode_stream(encoded) == (n,), 'integer roundtrip')
        require(decode_stream(encoded + g(0)) == (n, 0), 'integer boundary')
        if len(encoded) > 1:
            try:
                decode_stream(encoded[:-1])
                raise AssertionError('truncated integer accepted')
            except InvalidCode:
                pass
        COUNTS['integer_roundtrips'] += 1
    REGRESSIONS.append('gamma(n+1) exact lengths, concatenation, truncation, and up to 4097-bit payloads')


def check_source_length(source):
    sb = encode_source(source)
    tb = encode_target(canonical_target(source))
    require(decode_source(sb) == source, 'source roundtrip')
    require(decode_target(tb) == canonical_target(source), 'target roundtrip')
    formula = len(sb) + ell(3*source.m + 2) + ell(source.m) + ell(4*source.m) + 27*source.m + 4
    require(len(tb) == formula, 'exact sparse target length')
    if valid_source(source):
        require(reduce_bits(sb) == tb, 'valid reduction')
        require(len(tb) <= 4*len(sb) + 3, 'valid length bound')
        require(3*source.m*certificate_width(source.m) <= len(tb)**2, 'certificate polynomial length')
        COUNTS['valid_length_bound_cases'] += 1
    COUNTS['source_target_roundtrips'] += 1


def named_regressions():
    good = Source(2, 30, (9, 10, 11, 9, 10, 11))
    require(len(NO_BITS) == 129 and valid_source(NO_SOURCE), 'fixed NO data')
    require(check_certificate(encode_target(canonical_target(good)), encode_certificate((0,0,0,1,1,1), 2)),
            'good certificate rejected')
    require(not any(check_certificate(NO_BITS, encode_certificate(labels, 2))
                    for labels in product(range(2), repeat=6)), 'fixed NO certificate exists')
    empty = Source(0, 1, ())
    require(check_certificate(encode_target(canonical_target(empty)), ''), 'empty certificate rejected')
    require(not check_certificate(encode_target(canonical_target(empty)), '0'), 'extra empty-family bits')
    require(valid_source(good) and valid_source(NO_SOURCE) and valid_source(empty), 'valid named inputs')
    for source in (good, NO_SOURCE, empty, Source(2, 15, (4,)*6), Source(1, 4, (1,1,2))):
        check_source_length(source)
    REGRESSIONS.append('valid feasible/infeasible source, 129-bit fixed NO, m=0 empty certificate')

    malformed = ['', '0', '00', '2', g(0), encode_source(good)+'0', encode_source(good)+g(0),
                 encode_source(good)[:-1], encode_source(Source(0,0,())),
                 encode_source(Source(2,15,(4,)*6)), encode_source(Source(1,4,(1,1,2))),
                 g(2**100000)+g(1)]
    for bits in malformed:
        assert_rejected_source(bits)
    REGRESSIONS.append('malformed/truncated/trailing source, bad total/strict bounds, enormous m header')

    # These short inputs encode enormous sizes, but have too few supplied fields.
    target_bad = [g(2**100000)+g(0)+g(1), g(0)+g(0)+g(0),
                  NO_BITS+'0', NO_BITS+g(0), NO_BITS[:-1]]
    for bits in target_bad:
        require(not check_certificate(bits, ''), 'malformed target accepted')
        COUNTS['malformed_target_rejections'] += 1
    for cert in ('', '0', '1'*12, 'x'*12, '0000000000000'):
        require(not check_certificate(NO_BITS, cert), 'malformed or bad labels accepted')
        COUNTS['malformed_certificate_rejections'] += 1
    REGRESSIONS.append('enormous N header rejected before allocation, bad target lengths, invalid labels')

    # Canonical-shaped targets admit arbitrary natural leaf fees and budgets,
    # including zero fees/B. Feasibility is checked separately by certificates.
    # Source validity is deliberately not required.
    for source, labels in ((Source(2,0,(0,)*6), (0,)*6),
                           (Source(2,15,(4,)*6), (0,0,0,1,1,1)),
                           (Source(0,0,()), ())):
        target = canonical_target(source)
        require(has_h0_shape(target), 'canonical shape overrestricted')
        require(check_certificate(encode_target(target), encode_certificate(labels, source.m)),
                'canonical target valid assignment rejected')
        require(validate_routes(target, labels), 'accepted assignment did not reconstruct')
    routes = reconstruct_routes(canonical_target(Source(2,0,(0,)*6)), (0,)*6)
    require(routes[1] == (0,1,0), 'empty row is not hub-only')
    REGRESSIONS.append('accepted certificates for canonical targets with zero fees/B, underweight inputs, hub-only rows and zero-fleet B=0')


def exhaustive_valid_sources():
    for m in (1,2):
        for budget in range(1,17):
            allowed = tuple(a for a in range(1,budget+1) if budget < 4*a and 2*a < budget)
            for weights in product(allowed, repeat=3*m):
                if sum(weights) != m*budget:
                    continue
                source = Source(m,budget,weights)
                require(valid_source(source), 'generator source validity')
                check_source_length(source)
                target = canonical_target(source)
                target_bits = encode_target(target)
                source_answer = target_answer = False
                for labels in product(range(m), repeat=3*m):
                    three = is_three_partition(source, labels)
                    accept = check_certificate(target_bits, encode_certificate(labels, m))
                    require(three == accept, 'valid per-assignment iff')
                    source_answer |= three
                    target_answer |= accept
                    # Every assignment, not only feasible ones, reconstructs
                    # exact structural ledgers; budget agreement is checked too.
                    require(validate_routes(target, labels) == accept, 'route/certificate budget iff')
                    COUNTS['assignment_comparisons'] += 1
                require(source_answer == target_answer, 'existence iff')
                COUNTS['valid_small_sources'] += 1
                COUNTS['feasible_small_sources' if source_answer else 'infeasible_small_sources'] += 1
    REGRESSIONS.append('all valid sources for m in {1,2}, B in 1..16: assignment iff and exact route reconstruction')


def length_boundaries():
    rng = random.Random(20261107)
    for m in (0,1,2,3,4,7,8,15,16,31,32,63,64,127,128):
        for k in (0,1,2,3,7,8,15,16,31,32,63,64,127,128):
            a = 2**k
            # 3 equal positive items fill each bin and satisfy both strict bounds.
            check_source_length(Source(m, 3*a, (a,)*(3*m)))
    for _ in range(100):
        m = rng.randrange(0,25)
        a = rng.getrandbits(rng.randrange(1,513)) + 1
        check_source_length(Source(m, 3*a, (a,)*(3*m)))
    # A dense N*N flow matrix is not part of this encoding.
    target = canonical_target(Source(1,3,(1,1,1)))
    require(len(decode_stream(encode_target(target))) == 4*target.vertices+1,
            'sparse record count changed')
    REGRESSIONS.append('length transitions across m and weight bit boundaries; fixed-seed large integer cases; sparse field count')


def parser_and_totalization_tests():
    # General sparse trees decode independently of the restricted target shape.
    general = Target(4, 1, 9, (0,1,0), (1,2,0), (0,3,2,0), (7,1,2,0))
    bits = encode_target(general)
    require(decode_target(bits) == general, 'general sparse tree roundtrip')
    require(not has_h0_shape(general) and not check_certificate(bits, ''), 'noncanonical tree accepted')
    invalid_parent_values = [4,1,9, 0,1, 2,2, 0,0, 0,3,2,0, 7,1,2,0]
    invalid_parent_bits = ''.join(g(n) for n in invalid_parent_values)
    try:
        decode_target(invalid_parent_bits)
        raise AssertionError('parent p(v)=v accepted')
    except InvalidCode:
        pass
    require(not check_certificate(invalid_parent_bits, ''), 'invalid parent accepted by verifier')
    COUNTS['general_sparse_parser_cases'] += 2
    # Exhaust all short input strings, including the empty string. Valid codes
    # must be canonical and obey the valid branch bound; all others use NO.
    for length in range(13):
        for xs in product('01', repeat=length):
            sb = ''.join(xs)
            try:
                source = decode_source(sb)
                require(encode_source(source) == sb, 'source encoding not canonical')
                valid = valid_source(source)
            except InvalidCode:
                valid = False
            output = reduce_bits(sb)
            require(has_h0_shape(decode_target(output)), 'total reduction output lacks canonical shape')
            require(len(output) <= 4*len(sb)+129, 'all-input length bound')
            if valid:
                require(output == encode_target(canonical_target(source)), 'valid total branch')
                require(len(output) <= 4*len(sb)+3, 'valid short-code bound')
            else:
                require(output == NO_BITS, 'invalid total branch')
            COUNTS['short_input_totalization_cases'] += 1
    REGRESSIONS.append('general sparse tree roundtrip/noncanonical-shape rejection, parent-order rejection, every bitstring of length at most 12')


def main():
    COUNTS.clear()
    REGRESSIONS.clear()
    integer_tests()
    named_regressions()
    exhaustive_valid_sources()
    length_boundaries()
    parser_and_totalization_tests()
    report = dict(status='PASS', python=platform.python_version(),
                  counts=dict(COUNTS), fixed_no_target_bits=len(NO_BITS),
                  regressions=REGRESSIONS,
                  limits=['Finite Python checks; not a Lean kernel proof.',
                          'No Turing-machine or compiled runtime bound is tested.',
                          'Canonical-shape validation and certificate acceptance are separate; outputs are not all claimed feasible. Sparse parent/H representation only.',
                          'Large-header tests check bounded parser behavior, not general adversarial resource certification.'])
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
