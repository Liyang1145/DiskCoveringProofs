#!/usr/bin/env python3
"""Cross-check the exact threshold literals in `SevenClassQ0Deg3EdgeShape`.

The Lean file contains ten named strict rational comparisons of an edge
coefficient against `cosTQ 14` at a fixed grid node.  This audit parses those
names and recomputes every comparison with exact `Fraction` arithmetic.  It
also checks that the generic increasing-prefix helpers are declared before all
uses.  It checks source binding only; it is not a kernel proof.
"""
from __future__ import annotations

import hashlib
import json
import re
from fractions import Fraction as F
from math import factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean/N11Formalization/SevenClassQ0Deg3EdgeShape.lean"
DATA = HERE / "q0-degree3-piecewise-8.json"
OUT = HERE / "q0-degree3-edge-literals-audit.json"

EDGES = (
    (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8),
    (8, 0), (9, 0), (9, 1), (9, 10), (10, 0), (10, 1), (10, 2),
    (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8),
)
NUMBERS = {
    "zero": 0, "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
    "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10,
    "eleven": 11, "twelve": 12, "thirteen": 13, "fourteen": 14,
    "fifteen": 15, "sixteen": 16, "seventeen": 17, "eighteen": 18,
    "nineteen": 19, "twenty": 20,
}
PATTERN = re.compile(r"edge_ratio_([a-z]+)_lt_cosT14_nodeQ_(\d+)")
HELPERS = (
    "edgeIncTo_of_monotoneOn_to",
    "edgeIncTo_of_monotoneOn_to_prev_and_step",
)


def cos_tq(q: F) -> F:
    return sum(F((-1) ** k, factorial(2 * k)) * q ** (2 * k) for k in range(14))


def sin_hi(q: F) -> F:
    taylor = sum(
        F((-1) ** k) * q ** (2 * k + 1) / factorial(2 * k + 1)
        for k in range(14)
    )
    return taylor + abs(q) ** 29 / factorial(29)


def edge_upper(coefficient: F, q: F) -> F:
    return F(19, 50) ** 2 * sin_hi(q) - coefficient * q


def main() -> int:
    raw = DATA.read_bytes()
    data = json.loads(raw)
    mu = [F(value) for value in data["mu"]]
    pi_hi = F(data["piHi"])
    lean_raw = LEAN.read_bytes()
    lean_text = lean_raw.decode("utf-8")
    names = sorted(set(PATTERN.findall(lean_text)))
    failures = []
    rows = []
    steps = []
    helper_order = {}
    for helper in HELPERS:
        declarations = list(re.finditer(
            rf"^theorem {re.escape(helper)}\b", lean_text, re.MULTILINE
        ))
        uses = list(re.finditer(rf"\b{re.escape(helper)}\b", lean_text))
        if len(declarations) != 1:
            failures.append(
                f"{helper}: expected one declaration, got {len(declarations)}"
            )
            continue
        declaration = declarations[0].start()
        prior_uses = [match.start() for match in uses if match.start() < declaration]
        if prior_uses:
            failures.append(
                f"{helper}: {len(prior_uses)} use(s) precede its declaration"
            )
        helper_order[helper] = {
            "declaration_line": lean_text.count("\n", 0, declaration) + 1,
            "prior_uses": len(prior_uses),
        }
    if len(names) != 10:
        failures.append(f"expected 10 named threshold literals, got {len(names)}")
    for word, node_text in names:
        edge = NUMBERS[word]
        node = int(node_text)
        coefficient = sum(mu[j] for j in EDGES[edge])
        q = pi_hi * node / 2048
        rhs = cos_tq(q)
        lhs = coefficient / F(19, 50) ** 2
        if not lhs < rhs:
            failures.append(f"edge {edge} node {node}: {lhs} is not below {rhs}")
        rows.append({
            "edge": edge,
            "node": node,
            "coefficient": str(coefficient),
            "ratio": str(lhs),
            "cosTQ14": str(rhs),
            "strict": lhs < rhs,
        })
    for edge in (1, 8):
        coefficient = sum(mu[j] for j in data["edges"][edge]["edge"])
        prev = pi_hi * 877 / data["N"]
        peak = pi_hi * 878 / data["N"]
        before = edge_upper(coefficient, prev)
        after = edge_upper(coefficient, peak)
        if not before <= after:
            failures.append(f"edge {edge}: 877->878 step {before} <= {after} fails")
        steps.append({
            "edge": edge,
            "prev": 877,
            "peak": 878,
            "upperPrev": str(before),
            "upperPeak": str(after),
            "nondecreasing": before <= after,
        })
    report = {
        "scope": "exact decimal-free cross-check of Lean threshold literals; not a kernel proof",
        "lean_sha256": hashlib.sha256(lean_raw).hexdigest(),
        "data_sha256": hashlib.sha256(raw).hexdigest(),
        "rows": rows,
        "steps": steps,
        "helperOrder": helper_order,
        "allStrict": not failures,
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    if failures:
        print("FAIL")
        print("\n".join(failures))
        return 1
    print(f"PASS: {len(rows)} Lean edge-ratio literals and {len(steps)} endpoint steps")
    print(f"PASS: {len(helper_order)} generic helpers declared before all uses")
    print("sha256 json:", hashlib.sha256(OUT.read_bytes()).hexdigest())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
