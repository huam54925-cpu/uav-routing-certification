"""Bind existing Case1 inputs to Lean literals; never solve or evaluate the dual bound.

Run with --write to replace only the marked literal block in Case1Data.lean.
Run with --check to compare that block byte-for-byte (after newline normalization).
Python validates the JSON-to-literal boundary; it is not part of Lean's kernel.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent / "Case1Data.lean"
BEGIN = "-- BEGIN CASE1 LITERALS\n"
END = "-- END CASE1 LITERALS"
FINGERPRINT = "8edfbad732afb3501d0e2616946475be39d5f5540d335d215e829a66dd8b1ac8"


def rational(value):
    q = Fraction(value)
    return str(q.numerator) if q.denominator == 1 else f"({q.numerator} / {q.denominator})"


def vector(name, type_name, values):
    return f"def {name} : {type_name} :=\n  ![" + ",\n    ".join(values) + "]\n"


def literal_block():
    instance_path = HERE / "instances.json"
    certificate_path = HERE / "bound_Case1.json"
    instance = json.loads(instance_path.read_text(encoding="utf-8"))["cases"]["Case1"]
    record = json.loads(certificate_path.read_text(encoding="utf-8"))
    fingerprint = hashlib.sha256(json.dumps(instance, sort_keys=True).encode()).hexdigest()
    if fingerprint != FINGERPRINT or record["instance_sha256"] != fingerprint:
        raise ValueError("Case1 identity differs from the reviewed certificate")
    points = instance["points"]
    cert = record["certificate"]
    if record["fleet"] != 3 or len(points) != 52:
        raise ValueError("Wrong fleet or point count")
    if [p["id"] for p in points] != list(range(1, 53)):
        raise ValueError("Point order must equal node numbering 1..52")
    coords = [(0, 0)]
    for p in points:
        xy = tuple(Fraction(str(p[key])) for key in ("x", "y"))
        if any(q.denominator != 1 for q in xy):
            raise ValueError("This binding requires integer coordinates")
        coords.append(tuple(q.numerator for q in xy))
    required = [0] + [p["visits"] for p in points]
    if any(type(r) is not int or r <= 0 for r in required[1:]) or sum(required) != 72:
        raise ValueError("Unexpected inspection requirements")
    if Fraction(str(instance["unit_km"])) != Fraction(1, 10):
        raise ValueError("Coordinate units must be 0.1 km")
    if len(cert["eq_dual"]) != 106 or len(cert["cuts"]) != 32 or len(cert["cut_dual"]) != 32:
        raise ValueError("Wrong certificate dimensions")
    for cut in cert["cuts"]:
        if not cut or len(set(cut)) != len(cut) or any(type(i) is not int or not 1 <= i <= 52 for i in cut):
            raise ValueError("Invalid or duplicate cut member")
    if any(Fraction(z) > 0 for z in cert["cut_dual"]):
        raise ValueError("Positive cut multiplier")
    # Preserve all 32 positions, including rows with a zero multiplier.
    blocks = [
        "-- Case1 canonical instance SHA256: " + fingerprint,
        "-- instances.json SHA256: " + hashlib.sha256(instance_path.read_bytes()).hexdigest(),
        "-- bound_Case1.json SHA256: " + hashlib.sha256(certificate_path.read_bytes()).hexdigest(),
        vector("coordinates", "Node → ℤ × ℤ", [f"({x}, {y})" for x, y in coords]),
        vector("required", "Node → ℕ", list(map(str, required))),
        vector("eqDual", "Fin 106 → ℚ", [rational(q) for q in cert["eq_dual"]]),
        vector("cuts", "CutIndex → Finset Node", ["{" + ", ".join(map(str, s)) + "}" for s in cert["cuts"]]),
        vector("cutDual", "CutIndex → ℚ", [rational(q) for q in cert["cut_dual"]]),
        vector("cutWitness", "CutIndex → Node", [str(s[0]) for s in cert["cuts"]]),
    ]
    return BEGIN + "\n\n".join(blocks) + "\n" + END


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    text = LEAN.read_text(encoding="utf-8")
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise ValueError("Expected exactly one marked literal block")
    start = text.index(BEGIN)
    stop = text.index(END, start) + len(END)
    expected = literal_block()
    if args.write:
        LEAN.write_text(text[:start] + expected + text[stop:], encoding="utf-8", newline="\n")
    elif text[start:stop] != expected:
        raise ValueError("Lean literals differ from the original Case1 inputs")
    print("Case1 literal binding PASS: 53 nodes, 72 visits, 106 equality coefficients, 32 cuts/multipliers")
    print("Node ids, integer coordinates, exact rational coefficients and cut order checked; dual bound not evaluated")


if __name__ == "__main__":
    main()
