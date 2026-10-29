#!/usr/bin/env python3
"""Audit the concavity reduction for the q0 degree-three upper tables.

For nonnegative q, the derivative of `sinHiNLag q` is
`cosTQ 14 q + q^28 / 28!` (the `cosHiNLag` upper bracket).  Hence every edge
or sector upper function has derivative `R2 * cosHiNLag q - constant` (with an
extra factor 1/2 for sectors) on each fixed-node bin.  This script checks the
exact grid sign pattern and verifies that each recorded maximum is the unique
grid maximum predicted by the first sign crossing.  It is a data audit, not a
Lean proof.
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import probe_q0_degree3_nodes as probe  # noqa: E402

MANIFEST = HERE / "q0-degree3-piecewise-8.json"
OUT = HERE / "q0-degree3-concavity.json"


def cos_t(q: F) -> F:
    total, power, square = F(0), F(1), q * q
    for j in range(15):
        total += F((-1) ** j, probe.factorial(2 * j)) * power
        power *= square
    return total


def cos_hi(q: F) -> F:
    return cos_t(q) + q ** 28 / probe.factorial(28)


def edge_value(b: F, q: F) -> F:
    return probe.R2 * probe.sinHi(q) - b * q


def sector_value(mu: F, lam: F, q: F, a: F) -> F:
    return ((2 * a - probe.sinLo(2 * a)) / 2 + probe.R2 * probe.sinHi(q) / 2
            + 2 * lam * a - mu * q)


def sign(x: F) -> int:
    return (x > 0) - (x < 0)


def first_nonpositive_after_positive(derivs: list[F]) -> int:
    """Return the last index with derivative > 0, requiring +...+,0...-,...-."""
    signs = [sign(x) for x in derivs]
    first_zero_or_neg = next((i for i, s in enumerate(signs) if s <= 0), len(signs))
    if any(s > 0 for s in signs[first_zero_or_neg:]):
        raise AssertionError("derivative sign is not a single positive-to-nonpositive run")
    if any(s < 0 for s in signs[:first_zero_or_neg]):
        raise AssertionError("derivative sign is not positive before its first nonpositive value")
    return first_zero_or_neg - 1


def candidate_after_crossing(derivs: list[F], lo: int, hi: int) -> int:
    """Maximum of a concave grid sequence on [lo, hi]."""
    sub = derivs[lo:hi + 1]
    last_pos = first_nonpositive_after_positive(sub)
    if last_pos < 0:
        return lo
    if last_pos >= hi - lo:
        return hi
    left, right = lo + last_pos, lo + last_pos + 1
    # The continuous derivative changes sign inside this grid cell.  Concavity
    # puts the maximum at one of its endpoints; compare the two exact values.
    return left


def main() -> None:
    d = json.loads(MANIFEST.read_text())
    raw, row = probe.load()
    mu = [F(x) for x in d["mu"]]
    lam = F(d["lambda"])
    U = F(d["piHi"])
    assert (raw, row["q"]) == (raw, 0)
    qs = [U * k / probe.N for k in range(probe.N + 1)]

    chi = [cos_hi(q) for q in qs]
    monotone = all(chi[k + 1] <= chi[k] for k in range(probe.N))
    assert monotone, "cosHiNLag is not monotone nonincreasing on the exact grid"

    edges = {(i, (i + 1) % 9) for i in range(9)}
    edges |= {(9, 0), (9, 1), (9, 10), *((10, i) for i in range(9))}
    edge_records = []
    for item, edge in zip(d["edges"], sorted(edges)):
        assert tuple(item["edge"]) == edge
        b = sum(mu[i] for i in edge)
        derivs = [probe.R2 * c - b for c in chi]
        last_pos = first_nonpositive_after_positive(derivs)
        k = min(probe.N, max(0, last_pos + (0 if last_pos < 0 else 1)))
        if k > 0:
            k = max((k - 1, k), key=lambda j: edge_value(b, qs[j]))
        value = edge_value(b, qs[k])
        assert value == F(item["max"]), (edge, k, item["witnessK"])
        assert k == item["witnessK"], (edge, k, item["witnessK"])
        edge_records.append({"edge": list(edge), "maxGridK": k,
                             "derivativeLastPositiveK": last_pos,
                             "derivativeAtMax": str(derivs[k]),
                             "max": str(value)})

    bins = d["bins"]
    sector_records = []
    for i, item in enumerate(d["sectors"]):
        candidates = []
        for j, b in enumerate(bins):
            lo = j * probe.N // len(bins)
            hi = ((j + 1) * probe.N // len(bins)) if j + 1 < len(bins) else probe.N
            derivs = [probe.R2 * c / 2 - mu[i] for c in chi]
            k = candidate_after_crossing(derivs, lo, hi)
            choices = [k]
            if k < hi:
                choices.append(k + 1)
            k = max(choices, key=lambda j: sector_value(mu[i], lam, qs[j], F(b["node"])))
            candidates.append((sector_value(mu[i], lam, qs[k], F(b["node"])), k, j))
        value, k, j = max(candidates)
        assert value == F(item["max"]), (i, k, item["witnessK"], value, item["max"])
        assert k == item["witnessK"], (i, k, item["witnessK"])
        sector_records.append({"site": item["site"], "maxGridK": k,
                               "extremalBin": j, "max": str(value)})

    report = {
        "scope": "exact-rational concavity/sign-crossing audit; no Lean claim",
        "manifest_sha256": __import__("hashlib").sha256(MANIFEST.read_bytes()).hexdigest(),
        "N": probe.N,
        "piHi": str(U),
        "cosHiMonotoneNonincreasing": monotone,
        "edges": edge_records,
        "sectors": sector_records,
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print("cosHi monotone:", monotone)
    print("edge maxima confirmed:", len(edge_records))
    print("sector maxima confirmed:", len(sector_records))
    print("wrote", OUT.relative_to(probe.ROOT))


if __name__ == "__main__":
    main()
