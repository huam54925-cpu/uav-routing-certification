"""Independent exact audit of all Case1 non-diagonal arc costs.

Reads the pinned Lean coordinate literals directly (not the binding generator).
Compares a binary-search integer root of the Lean formula with the verifier's
Fraction/isqrt formula applied to the original JSON. Does not evaluate the dual
certificate, import a solver, or claim to execute Lean's compiled cost function.
"""
import argparse
import ast
from fractions import Fraction as Q
import hashlib
import json
from math import isqrt
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
LEAN_SHA256_LF = "cce161c618a2ae82df1b72850a27bf7f4cb7ba927a02c3ed7a87c094f2293f3d"
INSTANCE_SHA256 = "8edfbad732afb3501d0e2616946475be39d5f5540d335d215e829a66dd8b1ac8"


def binary_sqrt(n):
    """Independent floor square root, using only integer comparisons."""
    if n < 0:
        raise ValueError("Negative squared distance")
    lo, hi = 0, 1 << ((n.bit_length() + 1) // 2)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid * mid <= n:
            lo = mid
        else:
            hi = mid
    return lo


def audit(lean_path, instances_path):
    text = lean_path.read_text(encoding="utf-8")
    if hashlib.sha256(text.encode()).hexdigest() != LEAN_SHA256_LF:
        raise ValueError("Lean source differs from the reviewed Case1Data version (LF-normalized)")
    match = re.search(r"def coordinates : Node → ℤ × ℤ :=\s*!\[(.*?)\]\s*def required", text, re.S)
    if match is None:
        raise ValueError("Unexpected Lean coordinate literal syntax")
    lean_coords = ast.literal_eval("[" + match.group(1) + "]")
    if len(lean_coords) != 53 or any(
        not isinstance(p, tuple) or len(p) != 2 or any(type(v) is not int for v in p)
        for p in lean_coords
    ):
        raise ValueError("Expected 53 integral coordinate pairs")

    ins = json.loads(instances_path.read_text(encoding="utf-8"))["cases"]["Case1"]
    fingerprint = hashlib.sha256(json.dumps(ins, sort_keys=True).encode()).hexdigest()
    if fingerprint != INSTANCE_SHA256:
        raise ValueError("Wrong Case1 input identity")
    if [p["id"] for p in ins["points"]] != list(range(1, 53)):
        raise ValueError("Unexpected point numbering/order")
    json_coords = [(Q(0), Q(0))] + [(Q(str(p["x"])), Q(str(p["y"]))) for p in ins["points"]]
    if lean_coords != json_coords or Q(str(ins["unit_km"])) != Q(1, 10):
        raise ValueError("Coordinate or unit mismatch")
    if ins["speed_kmh"] != 55 or ins["limit_h"] != 9 or ins["service_h"] != 5 / 60:
        raise ValueError("Unexpected speed/time/service model constants")
    if sum(p["visits"] for p in ins["points"]) != 72:
        raise ValueError("Unexpected inspection count")

    # Test exact-square boundaries independently of the Case1 coordinates.
    for n in [0, 1, 2, 3, 4, 15, 16, 17, 10**20 - 1, 10**20, 10**20 + 1]:
        c = binary_sqrt(n)
        if not c * c <= n < (c + 1) * (c + 1):
            raise ValueError("Binary square-root boundary check failed")

    costs = {}
    factor = Q(str(ins["unit_km"])) * 1_000_000
    for i, (x, y) in enumerate(lean_coords):
        for j, (a, b) in enumerate(lean_coords):
            if i == j:
                continue
            # Integer interpretation of the pinned Lean squaredDistance/costUnits definitions.
            squared = (x - a)**2 + (y - b)**2
            scaled = squared * 10_000_000_000
            lean_formula_cost = binary_sqrt(scaled)
            # Independent original JSON path with rational scaling, as in the existing verifier.
            u, v = json_coords[i]
            w, z = json_coords[j]
            reference_squared = ((u - w)**2 + (v - z)**2) * factor**2
            reference_cost = isqrt(reference_squared.numerator // reference_squared.denominator)
            if scaled != reference_squared or lean_formula_cost != reference_cost:
                raise ValueError(f"Arc {(i, j)} coordinate/scale/cost mismatch")
            if not lean_formula_cost**2 <= reference_squared < (lean_formula_cost + 1)**2:
                raise ValueError(f"Arc {(i, j)} is not the exact lower integer root")
            costs[i, j] = lean_formula_cost
    if len(costs) != 2756 or any(c != costs[j, i] for (i, j), c in costs.items()):
        raise ValueError("Arc count or symmetry mismatch")
    print("Independent Case1 arc-cost audit PASS")
    print("Arcs=2756; coordinate/order/scale/exact-floor checks=2756; symmetry=PASS")
    print(f"Cost range in millionths of km: {min(costs.values())}..{max(costs.values())}")
    print("Budget inputs match: speed=55 km/h, service=5 min/visit, visits=72, limit=9 h")
    print("Offline formula audit; not a Lean runtime export or a dual-bound recomputation")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, default=HERE.parent / "Case1Data.lean")
    parser.add_argument("--instances", type=Path, default=HERE / "instances.json")
    args = parser.parse_args()
    audit(args.lean, args.instances)


if __name__ == "__main__":
    main()
