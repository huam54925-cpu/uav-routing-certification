"""Independent exact-arithmetic verification of a four-UAV Case1 witness.

Usage:
    py -3 verify_case1_feasible.py --instances PATH --solution PATH

No optimiser, Lean runtime, third-party packages, or floating-point feasibility test.
Actual Euclidean distances are conservatively UPPER-bounded by integer square roots.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from math import isqrt
import json
from pathlib import Path

CASE1_FINGERPRINT = "8edfbad732afb3501d0e2616946475be39d5f5540d335d215e829a66dd8b1ac8"
SCALE = 1_000_000  # integer units per km
SQUARED_SCALE = 10_000_000_000  # (0.1 km * 1e6 units/km) ** 2
SPEED = 55  # km/h
LIMIT = 9  # h
SERVICE_PER_VISIT = Fraction(1, 12)  # exactly five minutes


def require(condition: bool, explanation: str) -> None:
    if not condition:
        raise ValueError(explanation)


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def verify(instances_path: Path, solution_path: Path) -> None:
    data = load_json(instances_path)["cases"]["Case1"]
    canonical = json.dumps(data, sort_keys=True).encode("utf-8")
    require(sha256(canonical).hexdigest() == CASE1_FINGERPRINT,
            "Case1 instance fingerprint does not match the pinned certificate")
    require(Fraction(str(data["unit_km"])) == Fraction(1, 10), "coordinate units changed")
    require(Fraction(str(data["speed_kmh"])) == SPEED, "flight speed changed")
    require(Fraction(str(data["limit_h"])) == LIMIT, "working-time limit changed")
    # This JSON field stores the binary-float approximation of five minutes / 60.
    require(abs(Fraction(str(data["service_h"])) - SERVICE_PER_VISIT) < Fraction(1, 10**15),
            "service duration is not consistent with five minutes")

    points = data["points"]
    require(len(points) == 52 and [p["id"] for p in points] == list(range(1, 53)),
            "52 point IDs must be in their canonical order")
    coords = {0: (0, 0)}
    required = {}
    for p in points:
        x, y, n = p["x"], p["y"], p["visits"]
        require(type(n) is int and n > 0,
                f"point {p['id']} has unsupported visit count")
        try:
            xy = (Fraction(str(x)), Fraction(str(y)))
        except (ValueError, ZeroDivisionError) as exc:
            raise ValueError(f"point {p['id']} has unsupported coordinates") from exc
        require(all(q.denominator == 1 for q in xy),
                f"point {p['id']} requires integral coordinates")
        coords[p["id"]] = (xy[0].numerator, xy[1].numerator)
        required[p["id"]] = n
    require(sum(required.values()) == 72, "expected visit total must be 72")

    answer = load_json(solution_path)["Case1"]
    routes = answer["routes"]
    require(type(routes) is list and len(routes) == 4 and answer["N"] == 4,
            "expected exactly four routes and N=4")
    require(sorted(r["uav"] for r in routes) == [1, 2, 3, 4],
            "vehicle identifiers must be 1, 2, 3, 4")

    counts = Counter()
    rows = []
    total_lower = total_upper = 0
    # Multiplication by 12 * 55 * 1e6 makes the exact time test entirely integral.
    budget_integer = LIMIT * 12 * SPEED * SCALE
    for route in routes:
        k = route["uav"]
        seq = route["sequence"]
        require(type(seq) is list and len(seq) >= 3, f"UAV{k}: empty/invalid route")
        require(all(type(v) is int and v in coords for v in seq),
                f"UAV{k}: invalid physical node ID")
        require(seq[0] == seq[-1] == 0, f"UAV{k}: not depot-to-depot")
        require(0 not in seq[1:-1], f"UAV{k}: intermediate depot visit")
        require(all(a != b for a, b in zip(seq, seq[1:])),
                f"UAV{k}: consecutive equal nodes")
        tasks = seq[1:-1]
        require(route["service_count"] == len(tasks),
                f"UAV{k}: stored service_count contradicts route")
        counts.update(tasks)

        lower = upper = 0
        for a, b in zip(seq, seq[1:]):
            xa, ya = coords[a]
            xb, yb = coords[b]
            squared = ((xa - xb) ** 2 + (ya - yb) ** 2) * SQUARED_SCALE
            floor_root = isqrt(squared)
            ceil_root = floor_root + (floor_root * floor_root < squared)
            require(floor_root ** 2 <= squared <= ceil_root ** 2,
                    f"UAV{k}: bad integer-root bracket")
            lower += floor_root
            upper += ceil_root

        # Strict upper bound on actual flight + service time, no floating-point comparison.
        lhs = 12 * upper + SPEED * SCALE * len(tasks)
        require(lhs <= budget_integer, f"UAV{k}: cannot certify nine-hour feasibility")
        t_upper = Fraction(upper, SCALE * SPEED) + SERVICE_PER_VISIT * len(tasks)
        slack = Fraction(budget_integer - lhs, 12 * SCALE * SPEED)
        rows.append((k, len(tasks), lower, upper, t_upper, slack))
        total_lower += lower
        total_upper += upper

    mismatches = {i: (required[i], counts[i]) for i in required if required[i] != counts[i]}
    require(not mismatches, f"per-site coverage mismatch: {mismatches}")
    require(sum(counts.values()) == 72, "overall inspection count mismatch")

    print("Independent Case1 four-UAV feasibility certificate PASS")
    print("Pinned instance fingerprint PASS; depot/IDs/adjacency PASS; exact 52-point coverage PASS")
    print("Exact per-leg Euclidean upper bounds use only integer isqrt; no time tolerances")
    for k, n, lower, upper, t_upper, slack in rows:
        print(f"UAV{k}: visits={n:2d}; "
              f"distance_km=[{lower / SCALE:.6f}, {upper / SCALE:.6f}]; "
              f"time_h <= {float(t_upper):.10f}; "
              f"slack_min >= {float(slack) * 60:.6f}")
    print(f"Total flown distance lies between {total_lower / SCALE:.6f} "
          f"and {total_upper / SCALE:.6f} km")
    print("Conclusion for the specified Case1 physics: a feasible 4-UAV witness exists (N_min <= 4)")
    print("Not a Lean kernel verification or a proof that 4 is the minimum")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--instances", type=Path, required=True)
    parser.add_argument("--solution", type=Path, required=True)
    args = parser.parse_args()
    try:
        verify(args.instances, args.solution)
    except (ValueError, KeyError, TypeError, IndexError, json.JSONDecodeError) as ex:
        parser.exit(1, f"Case1 feasibility certificate FAIL: {ex}\n")


if __name__ == "__main__":
    main()
