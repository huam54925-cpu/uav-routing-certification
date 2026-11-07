"""Finite, exact-rational model checks for the Issue 19 paper contract.

This is an independent Python experiment, not a Lean proof or exhaustive
verification of unbounded inputs. Uses only the Python standard library.
Run from the repository root; results go to stdout and no files are written.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product, permutations
import json
import platform


VERTICES = ("o", "x", "h", "a", "b", "c", "d")
LEAVES = ("a", "b")
INSIDE = frozenset(("h", *LEAVES))
EDGES = {frozenset(e) for e in [("o", "x"), ("x", "h"),
         ("h", "a"), ("h", "b"), ("x", "c"), ("x", "d")]}
COUNTS = Counter()
REGRESSIONS = []


def need(condition, message):
    if not condition:
        raise AssertionError(message)


def words(alphabet, limit):
    return [word for n in range(limit + 1) for word in product(alphabet, repeat=n)]


def inside(word):
    out = ["h"]
    for a in word:
        out.extend((a, "h"))
    return tuple(out)


def flow(route):
    return Counter(zip(route, route[1:]))


def visits(route):
    return Counter(v for v in route if v != "o")


def plus(counters):
    out = Counter()
    for c in counters:
        out.update(c)
    return out


def service(route, fees):
    return sum((fees[v] for v in route if v != "o"), Q(0))


def chain(route):
    return all(frozenset((a, b)) in EDGES for a, b in zip(route, route[1:]))


def legal(route):
    return (len(route) >= 3 and route[0] == route[-1] == "o"
            and "o" not in route[1:-1] and chain(route))


def valid_slot(u, v):
    return (len(u) >= 2 and len(v) >= 2 and u[0] == "o" and u[-1] == "x"
            and v[0] == "x" and v[-1] == "o" and "o" not in u[1:]
            and "o" not in v[:-1] and not (set(u) | set(v)) & INSIDE
            and chain(u) and chain(v))


def split(route):
    """Identify separator edge occurrences directly in a full route."""
    if not legal(route):
        raise ValueError("illegal full route")
    ent = [i for i, e in enumerate(zip(route, route[1:])) if e == ("x", "h")]
    ext = [i for i, e in enumerate(zip(route, route[1:])) if e == ("h", "x")]
    if len(ent) != 1 or len(ext) != 1 or ent[0] >= ext[0]:
        raise ValueError("not one paired excursion")
    e, z = ent[0], ext[0]
    u, w, v = route[:e + 1], route[e + 1:z + 1], route[z + 1:]
    if not valid_slot(u, v) or not set(w) <= INSIDE:
        raise ValueError("piece support violation")
    if not (w[0] == w[-1] == "h" and chain(w)):
        raise ValueError("invalid inner walk")
    need(u + w + v == route, "split lost list occurrences")
    return u, w, v


def matrix_row(word, fees):
    n = Counter(word)
    demand = Counter({"h": 1 + len(word)}) + n
    f = Counter({("x", "h"): 1, ("h", "x"): 1})
    for a, count in n.items():
        f[("h", a)] = count
        f[(a, "h")] = count
    cost = fees["h"] + sum(((fees[a] + fees["h"]) * n[a] for a in LEAVES), Q(0))
    return demand, f, cost


def fees(**overrides):
    ans = {v: Q(0) for v in VERTICES}
    ans.update({v: Q(q) for v, q in overrides.items()})
    return ans


def aggregate_rows(rows):
    return plus(r[0] for r in rows), plus(r[1] for r in rows)


def compatible(rows, slots, s, d, f, budget, allowed, fixed=()):
    di, fi = aggregate_rows(rows)
    do = plus(visits(p) for uv in slots for p in uv)
    fo = plus(flow(p) for uv in slots for p in uv)
    do.update(plus(visits(r) for r in fixed))
    fo.update(plus(flow(r) for r in fixed))
    if do + di != d or fo + fi != f or any(service(r, s) > budget for r in fixed):
        return False
    b = [service(u, s) + service(v, s) for u, v in slots]
    return any(all(b[j] + rows[i][2] <= budget for j, i in enumerate(pi))
               for pi in allowed)


def actual_glue(word_family, slots, s, d, f, budget, allowed, fixed=()):
    for pi in allowed:
        if len(pi) != len(slots) or sorted(pi) != list(range(len(word_family))):
            continue
        routes = tuple(u + inside(word_family[pi[j]]) + v for j, (u, v) in enumerate(slots)) + fixed
        if (all(legal(r) for r in routes) and plus(visits(r) for r in routes) == d
                and plus(flow(r) for r in routes) == f
                and all(service(r, s) <= budget for r in routes)):
            return True
    return False


def named_regressions():
    slots = ((("o", "x", "c", "x"), ("x", "o")),
             (("o", "x", "d", "x"), ("x", "o")))
    s = fees(a=3, b=3, c=4, d=4)
    bad, good = (("a", "b"), ()), (("a",), ("b",))
    rs = [matrix_row(w, s) for w in good]
    full = [u + inside(w) + v for w, (u, v) in zip(good, slots)]
    d, f = plus(visits(r) for r in full), plus(flow(r) for r in full)
    both = list(permutations(range(2)))
    need(not actual_glue(bad, slots, s, d, f, Q(7), both), "original bad accepted")
    need(actual_glue(good, slots, s, d, f, Q(7), both), "original good rejected")
    need(d["x"] == 6 and d["h"] == 4, "original demand mismatch")
    need(aggregate_rows(rs) == aggregate_rows([matrix_row(w, s) for w in bad]), "old aggregate differs")
    REGRESSIONS.append("original separation, including exact x=6 and h=4 demand")

    s2 = fees(a=3, b=3, c=4, d=4, x=Q(1, 2), h=Q(-2, 3))
    need([service(u, s2) + service(v, s2) for u, v in slots] == [Q(11, 2)] * 2, "x occurrence lost")
    need([matrix_row(w, s2)[2] for w in bad] == [Q(4), Q(-2, 3)], "hub charges bad")
    need([matrix_row(w, s2)[2] for w in good] == [Q(5, 3)] * 2, "hub charges good")
    REGRESSIONS.append("nonzero rational boundary and hub charges")

    need(inside(()) == ("h",) and visits(inside(()))["h"] == 1, "singleton hub doubled")
    need(flow(("x",) + inside(()) + ("x",)) == Counter({("x", "h"): 1, ("h", "x"): 1}), "singleton flow")
    REGRESSIONS.append("hub-only excursion with one hub service occurrence")

    negative = fees(a=10, x=-2)
    slot = ((("o", "x"), ("x", "o")),)
    route = ("o", "x", "h", "a", "h", "x", "o")
    need(matrix_row(("a",), negative)[2] == 10 and service(route, negative) == 6, "cancellation counts")
    need(actual_glue((("a",),), slot, negative, visits(route), flow(route), Q(7), [(0,)]), "negative cancellation rejected")
    REGRESSIONS.append("signed cancellation: c=10, b=-4, T=7 accepted")

    s3 = fees(a=2, b=1, c=6, d=0)
    rs3 = [matrix_row(w, s3) for w in good]
    need(not compatible(rs3, slots, s3, d, f, Q(7), [(0, 1)]), "forbidden exchange accepted")
    need(compatible(rs3, slots, s3, d, f, Q(7), both), "permitted exchange rejected")
    need(not actual_glue(good, slots, s3, d, f, Q(7), [(0, 1)]), "fixed actual accepts")
    need(actual_glue(good, slots, s3, d, f, Q(7), both), "exchange actual rejects")
    REGRESSIONS.append("fixed ownership versus allowed joint exchange")

    twice = ("o", "x", "h", "a", "h", "x", "c", "x", "h", "x", "o")
    need(legal(twice), "two-excursion route should be legal globally")
    try:
        split(twice)
        raise AssertionError("two excursions accepted into restricted domain")
    except ValueError:
        pass
    REGRESSIONS.append("globally legal two-excursion route rejected from restricted domain")

    need(compatible([], (), s, Counter(), Counter(), Q(-1), [()]), "empty family rejected")
    need(actual_glue((), (), s, Counter(), Counter(), Q(-1), [()]), "empty actual family rejected")
    need(not compatible([], (), s, Counter(), Counter(), Q(-1), []), "empty Gamma accepted")
    fixed = (("o", "x", "c", "x", "o"),)
    fd, ff = visits(fixed[0]), flow(fixed[0])
    need(compatible([], (), s, fd, ff, Q(4), [()], fixed), "nonparticipant not counted")
    need(not compatible([], (), s, fd, ff, Q(3), [()], fixed), "nonparticipant budget ignored")
    need(actual_glue((), (), s, fd, ff, Q(4), [()], fixed), "fixed-only family rejected")
    REGRESSIONS.append("empty participants, empty Gamma, nonparticipant totals and budget")

    need(words((), 4) == [()], "empty leaf alphabet has spurious word")
    need(matrix_row((), s)[0] == Counter({"h": 1}), "empty leaves do not give hub only")
    REGRESSIONS.append("empty leaf set retains hub-only excursions")

    w1, w2 = ("a", "b"), ("b", "a")
    need(inside(w1) != inside(w2) and matrix_row(w1, s2) == matrix_row(w2, s2), "order example invalid")
    REGRESSIONS.append("distinct leaf orders have identical retained interface")

    depot_fee = dict(s)
    depot_fee["o"] = Q(1000)
    need(all(service(r, depot_fee) == service(r, s) for r in full), "depot fee was charged")
    REGRESSIONS.append("nonzero depot fee is excluded from service cost")

    # Correct total internal cost is insufficient for realizability per row.
    impossible_fees = fees(a=2)
    feasible_costs = set()
    for family in product(words(("a",), 1), repeat=2):
        if sum(w.count("a") for w in family) == 1:
            feasible_costs.add(tuple(service(inside(w), impossible_fees) for w in family))
    need(feasible_costs == {(Q(2), Q(0)), (Q(0), Q(2))}, "unit leaf realizations wrong")
    need((Q(1), Q(1)) not in feasible_costs and sum((Q(1), Q(1))) == 2, "forged vector not rejected")
    REGRESSIONS.append("unrealizable cost vector (1,1) with k=2, H(a)=1, s(a)=2")


def exhaustive_gluing():
    ws = words(LEAVES, 3)
    slot_options = [(("o", "x"), ("x", "o")),
                    (("o", "x", "c", "x"), ("x", "o")),
                    (("o", "x"), ("x", "d", "x", "o")),
                    (("o", "x", "c", "x"), ("x", "d", "x", "o"))]
    schedules = [fees(a=3, b=3, c=4, d=4),
                 fees(a=Q(1, 2), b=Q(-3, 2), h=Q(2, 3), x=Q(-1, 2), c=2, d=-3),
                 fees(a=-2, b=-1, h=-1, x=-2, c=3, d=2),
                 fees(a=1, b=2, h=3, x=1, c=-4, d=-5)]
    budgets = [Q(-2), Q(0), Q(1, 2), Q(3), Q(7), Q(10)]
    matches = [(0, 1), (1, 0)]
    groups = {}
    for sidx, s in enumerate(schedules):
        for word_family in product(ws, repeat=2):
            rows = tuple(matrix_row(w, s) for w in word_family)
            di, fi = aggregate_rows(rows)
            sig = (sidx, tuple(sorted(di.items())), tuple(sorted(fi.items())), tuple(r[2] for r in rows))
            outcomes = []
            for slots in product(slot_options, repeat=2):
                need(all(valid_slot(*uv) for uv in slots), "invalid generated context")
                do = plus(visits(p) for uv in slots for p in uv)
                fo = plus(flow(p) for uv in slots for p in uv)
                target_d, target_f = di + do, fi + fo
                base = [service(u, s) + service(v, s) for u, v in slots]
                costs_by_pi = []
                for pi in matches:
                    actual = []
                    for j, (u, v) in enumerate(slots):
                        w = inside(word_family[pi[j]])
                        r = u + w + v
                        need(legal(r), "glued route illegal")
                        need(split(r) == (u, w, v), "extraction round trip failed")
                        need(visits(r) == visits(u) + rows[pi[j]][0] + visits(v), "visit identity")
                        need(flow(r) == flow(u) + rows[pi[j]][1] + flow(v), "flow identity")
                        need(service(r, s) == base[j] + rows[pi[j]][2], "service identity")
                        actual.append(r)
                        COUNTS["route_identity_and_extraction_cases"] += 1
                    need(plus(visits(r) for r in actual) == target_d, "family demand identity")
                    need(plus(flow(r) for r in actual) == target_f, "family flow identity")
                    costs_by_pi.append(tuple(service(r, s) for r in actual))
                for budget in budgets:
                    fixed_actual = all(c <= budget for c in costs_by_pi[0])
                    all_actual = any(all(c <= budget for c in costs) for costs in costs_by_pi)
                    fixed_interface = all(base[j] + rows[j][2] <= budget for j in range(2))
                    all_interface = any(all(base[j] + rows[pi[j]][2] <= budget for j in range(2)) for pi in matches)
                    need((fixed_actual, all_actual) == (fixed_interface, all_interface), "compatibility iff")
                    outcomes.extend((fixed_actual, all_actual))
                    COUNTS["budget_and_matching_iff_cases"] += 2
                # Wrong exact targets reject, even with a permissive budget.
                wrong_d = target_d.copy()
                wrong_d["h"] += 1
                wrong_f = target_f.copy()
                wrong_f[("o", "o")] += 1
                need(not compatible(rows, slots, s, wrong_d, target_f, Q(100), matches), "wrong demand accepted")
                need(not compatible(rows, slots, s, target_d, wrong_f, Q(100), matches), "wrong flow accepted")
                need(not actual_glue(word_family, slots, s, wrong_d, target_f, Q(100), matches), "actual wrong demand accepted")
                need(not actual_glue(word_family, slots, s, target_d, wrong_f, Q(100), matches), "actual wrong flow accepted")
                COUNTS["mutated_exact_target_rejections"] += 2
                COUNTS["family_context_fee_cases"] += 1
            if sig in groups:
                need(groups[sig] == outcomes, "same-interface contextual replacement failed")
                COUNTS["same_interface_family_comparisons"] += 1
            else:
                groups[sig] = outcomes
    COUNTS["distinct_interfaces_in_order_test"] = len(groups)


def realizability_checks():
    # For fixed H and number of excursions k, enumerate both words (orderful)
    # and bounded natural matrices (orderless), then compare their whole images.
    s = fees(h=Q(-1, 2), a=Q(3, 2), b=Q(-1, 3))
    for k in range(3):
        for ha, hb in product(range(3), repeat=2):
            hcounts = {"a": ha, "b": hb}
            ws = words(LEAVES, ha + hb)
            word_image = set()
            for family in product(ws, repeat=k):
                counts = plus(Counter(w) for w in family)
                if any(counts[a] != hcounts[a] for a in LEAVES):
                    continue
                walk_family = [inside(w) for w in family]
                d = plus(visits(w) for w in walk_family)
                f = plus(flow(("x",) + w + ("x",)) for w in walk_family)
                costs = tuple(service(w, s) for w in walk_family)
                word_image.add((tuple(sorted(d.items())), tuple(sorted(f.items())), costs))
                COUNTS["realizability_ordered_witnesses"] += 1
            row_options = list(product(range(ha + 1), range(hb + 1)))
            matrix_image = set()
            for ns in product(row_options, repeat=k):
                if sum(n[0] for n in ns) != ha or sum(n[1] for n in ns) != hb:
                    continue
                d = Counter({"h": k + ha + hb, "a": ha, "b": hb})
                f = Counter({("x", "h"): k, ("h", "x"): k,
                             ("h", "a"): ha, ("a", "h"): ha,
                             ("h", "b"): hb, ("b", "h"): hb})
                # Remove zero-valued keys, matching direct list counters.
                d, f = +d, +f
                costs = tuple(s["h"] + (s["a"] + s["h"]) * na
                              + (s["b"] + s["h"]) * nb for na, nb in ns)
                matrix_image.add((tuple(sorted(d.items())), tuple(sorted(f.items())), costs))
                COUNTS["realizability_matrices"] += 1
            need(word_image == matrix_image, "Realizes matrix image differs from legal-list image")
            COUNTS["realizability_parameter_cases"] += 1
    REGRESSIONS.append("full realizability image equality for k,H(a),H(b) in {0,1,2}")


def main():
    COUNTS.clear()
    REGRESSIONS.clear()
    named_regressions()
    exhaustive_gluing()
    realizability_checks()
    report = {
        "status": "PASS", "python": platform.python_version(),
        "arithmetic": "exact fractions.Fraction rational arithmetic",
        "scope": {"internal_leaves": ["a", "b"], "max_leaf_word_length_per_excursion": 3,
                  "ordered_words": 15, "participating_routes": 2,
                  "exterior_slots_per_route": 4, "fee_schedules": 4,
                  "budgets": ["-2", "0", "1/2", "3", "7", "10"],
                  "matching_modes": ["fixed identity", "all two bijections"],
                  "realizability_range": "k, H(a), H(b) independently in {0,1,2}"},
        "counts": dict(COUNTS), "regressions": REGRESSIONS,
        "limitations": ["Finite Python checks only; not a Lean kernel proof.",
                        "No claim about arbitrary trees, repeated excursions, minimal interfaces, or complexity.",
                        "No LaTeX compilation or repository-wide Lean build performed."]}
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
