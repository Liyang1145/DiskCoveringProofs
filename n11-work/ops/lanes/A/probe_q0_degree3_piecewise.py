#!/usr/bin/env python3
"""Exact-rational eight-bin node candidate for the q0 degree-three certificate.

The node curve is constant on eight equal q-bins.  Each value is the smallest
decimal (denominator 10000) for which the source Taylor lower bound satisfies
the `NodeValid` inequality at the bin's upper endpoint.  This is a feasibility
manifest for Lean emission, not a Lean proof.
"""
from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import probe_q0_degree3_nodes as probe  # noqa: E402

OUT = HERE / "q0-degree3-piecewise-8.json"
BINS = 8


def ceil_10000(x: F) -> F:
    return F((x.numerator * 10000 + x.denominator - 1) // x.denominator, 10000)


def max_on_grid(f, qs, lo: F, hi: F):
    best = None
    for k, q in enumerate(qs):
        if lo <= q <= hi:
            value = f(q)
            if best is None or value > best[0]:
                best = (value, k, q)
    assert best is not None
    return best


def main() -> None:
    raw, row = probe.load()
    mu = [probe.mid(x) for x in row["mu"]]
    lam = probe.mid(row["lambda"])
    U, piLo = probe.interval(row["pi_interval"])[1], probe.interval(row["pi_interval"])[0]
    assert len(mu) == 11 and lam >= 0

    qs = [U * k / probe.N for k in range(probe.N + 1)]
    sin_hi = [probe.sinHi(q) for q in qs]
    width = F(U, probe.N)
    edges = {(i, (i + 1) % 9) for i in range(9)}
    edges |= {(9, 0), (9, 1), (9, 10), *((10, i) for i in range(9))}

    bins = []
    for j in range(BINS):
        lo, hi = U * j / BINS, U * (j + 1) / BINS
        cap, cap_k, cap_q = max_on_grid(probe.capQ, qs, lo, hi)
        left, right = F(0), F(1)
        for _ in range(24):
            mid = (left + right) / 2
            if probe.sinLo(mid) >= cap:
                right = mid
            else:
                left = mid
        node = ceil_10000(right)
        assert probe.sinLo(node) >= cap
        bins.append({
            "index": j,
            "qLo": str(lo),
            "qHi": str(hi),
            "capAtHi": str(cap),
            "capWitnessK": cap_k,
            "capWitnessQ": str(cap_q),
            "node": str(node),
        })

    def node(k: int) -> F:
        return F(bins[min(BINS - 1, BINS * k // probe.N)]["node"])

    nodes = [node(k) for k in range(probe.N + 1)]
    assert all(probe.sinLo(a) >= probe.capQ(q) for q, a in zip(qs, nodes))

    edge_data = []
    edge_max = {}
    for edge in sorted(edges):
        b = sum(mu[i] for i in edge)
        value, k, q = max_on_grid(
            lambda q, b=b: probe.R2 * probe.sinHi(q) - b * q, qs, F(0), U)
        edge_max[edge] = value
        edge_data.append({"edge": list(edge), "max": str(value), "witnessK": k,
                          "witnessQ": str(q)})

    sector_data = []
    sector_max = []
    for i in range(9):
        mu_i = mu[i]
        value, k, q = max_on_grid(
            lambda q, i=i: (2 * nodes[k_of(qs, q)] - probe.sinLo(2 * nodes[k_of(qs, q)])) / 2
            + probe.R2 * probe.sinHi(q) / 2 + 2 * lam * nodes[k_of(qs, q)] - mu[i] * q,
            qs, F(0), U)
        sector_max.append(value)
        sector_data.append({"site": i, "mu": str(mu_i), "max": str(value),
                            "witnessK": k, "witnessQ": str(q)})

    total = 2 * (sum(mu) - lam) * piLo
    for edge in edges:
        b = sum(mu[i] for i in edge)
        total += edge_max[edge] + (probe.R2 + abs(b)) * width
    for i in range(9):
        total += sector_max[i] + (1 + lam + abs(mu[i])) * width

    report = {
        "scope": "exact-rational eight-bin q0 degree-three node feasibility; no Lean claim",
        "source": str(probe.SRC.relative_to(probe.ROOT)),
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "N": probe.N,
        "binCount": BINS,
        "piLo": str(piLo),
        "piHi": str(U),
        "mu": [str(x) for x in mu],
        "lambda": str(lam),
        "bins": bins,
        "nodeValidAllGrid": True,
        "edges": edge_data,
        "sectors": sector_data,
        "totalUpper": str(total),
        "strictBelowPiLo": total < piLo,
        "slack": str(piLo - total),
    }
    assert total < piLo
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print("node values:", [b["node"] for b in bins])
    print("node_valid:", report["nodeValidAllGrid"])
    print("strict:", report["strictBelowPiLo"], "slack/piLo:", float((piLo - total) / piLo))
    print("wrote", OUT.relative_to(probe.ROOT))


def k_of(qs, q: F) -> int:
    return qs.index(q)


if __name__ == "__main__":
    main()
