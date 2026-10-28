#!/usr/bin/env python3
"""Exact-rational probe of simplified q0 degree-three area-grid node families.

Source multipliers are rounded outward decimal intervals.  We use interval
midpoints as exact rational multipliers, U = piHi, and N = 2048.  This is a
feasibility probe for future certificate emission, not a Lean proof.
"""
from __future__ import annotations
import hashlib, json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
SRC = ROOT / "cover11/proof_bundle/research-2026/team-current/lead/degree3_area_certificate.json"
OUT = Path(__file__).with_name("q0-degree3-node-probe.json")
N, R2 = 2048, F(19, 50) ** 2

def interval(text):
    lo, hi = text.strip()[1:-1].split(",")
    return F(lo), F(hi)

def mid(text):
    lo, hi = interval(text)
    return (lo + hi) / 2

def sinT(q):
    total, power, square = F(0), q, q * q
    for j in range(15):
        total += F((-1) ** j, factorial(2 * j + 1)) * power
        power *= square
    return total

def sinHi(q): return sinT(q) + abs(q) ** 29 / factorial(29)
def sinLo(q): return sinT(q) - abs(q) ** 29 / factorial(29)
def capQ(q): return F(19, 50) * max(F(1, 2), min(F(1), sinHi(q / 2)))

def load():
    raw = SRC.read_bytes()
    data = json.loads(raw)
    row, = [x for x in data["results"] if x["q"] == 0]
    assert data["N"] == N and row["strict_less_pi"]
    return raw, row

def main():
    raw, row = load()
    mu = [mid(x) for x in row["mu"]]
    lam = mid(row["lambda"])
    U, piLo = interval(row["pi_interval"])[1], interval(row["pi_interval"])[0]
    assert lam >= 0
    qs = [U * k / N for k in range(N + 1)]
    sh = [sinHi(q) for q in qs]
    h = F(U, N)
    edges = {(i, (i + 1) % 9) for i in range(9)}
    edges |= {(9, 0), (9, 1), (9, 10), *((10, i) for i in range(9))}
    edgeMax = {e: max(R2 * s - sum(mu[i] for i in e) * q
                     for s, q in zip(sh, qs)) for e in edges}

    def total(node):
        sectorMax = [max((2 * a - sinLo(2 * a)) / 2 + R2 * s / 2 + 2 * lam * a
                         - mu[i] * q for s, q, a in zip(sh, qs, node))
                     for i in range(9)]
        value = 2 * (sum(mu) - lam) * piLo
        for e in edges:
            b = sum(mu[i] for i in e)
            value += edgeMax[e] + (R2 + abs(b)) * h
        for i in range(9):
            value += sectorMax[i] + (1 + lam + abs(mu[i])) * h
        return value

    cases = []
    for name, node in [
        ("constant_2_5", [F(2, 5)] * (N + 1)),
        ("affine_192_plus_q_16", [F(192, 1000) + q / 16 for q in qs]),
    ]:
        valid = all(sinLo(a) >= capQ(q) for q, a in zip(qs, node))
        value = total(node)
        cases.append({"name": name, "node_valid": valid, "total": str(value),
                      "strict_below_piLo": value < piLo})
    report = {
        "scope": "exact-rational candidate-node feasibility only; no Lean claim",
        "source": str(SRC.relative_to(ROOT)),
        "source_sha256": hashlib.sha256(raw).hexdigest(), "N": N,
        "piLo": str(piLo), "piHi": str(U),
        "cases": cases,
        "conclusion": "constant 2/5 is node-valid but not strict; affine near-optimal fails NodeValid"
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    for c in cases:
        print(c["name"], "node_valid", c["node_valid"], "strict", c["strict_below_piLo"])
    print("wrote", OUT.relative_to(ROOT))

if __name__ == "__main__":
    main()
