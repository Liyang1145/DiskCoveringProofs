#!/usr/bin/env python3
"""Exact check: on each of the eight q-bins, capQ is maximised at the bin's
last grid node, and sinLoNLag at the constant node exceeds that maximum by a
positive exact margin.  This is the finite reduction a Lean bin table needs:
node_valid on 2049 nodes follows from 8 endpoint comparisons (plus the
monotonicity fact, which is NOT checked here)."""
from __future__ import annotations
import hashlib, json
from fractions import Fraction as F
from pathlib import Path
import probe_q0_degree3_nodes as probe

SRC = Path(__file__).with_name("q0-degree3-piecewise-8.json")

def main() -> None:
    d = json.loads(SRC.read_text())
    N = d["N"]; U = F(d["piHi"])
    bins = [(F(b["qLo"]), F(b["qHi"]), F(b["node"])) for b in d["bins"]]
    assert len(bins) == 8
    qs = [probe.capQ(U * k / N) for k in range(N + 1)]
    out = []
    covered = set()
    for i, (lo, hi, a) in enumerate(bins):
        ks = [k for k in range(N + 1) if lo <= U * k / N <= hi]
        k0, k1 = ks[0], ks[-1]
        assert min(ks) == k0 and max(ks) == k1
        assert k0 <= k1
        assert U * k1 / N == hi, (i, U * k1 / N, hi)
        m = max(qs[k] for k in ks)
        # check the maximum is attained exactly at the last grid node
        assert qs[k1] == m
        assert all(qs[k] <= m for k in ks)
        assert k1 not in covered
        covered |= set(ks)
        slack = probe.sinLo(a) - m
        assert slack > 0
        out.append({"bin": i, "kLo": k0, "kHi": k1, "count": len(ks),
                    "capMax": str(m), "capMaxK": k1,
                    "node": str(a), "sinLoNode": str(probe.sinLo(a)),
                    "slack": str(slack), "slackPositive": True})
    assert covered == set(range(N + 1))
    rep = {"scope": "exact per-bin endpoint maximum of capQ and positive NodeValid margin; "
                    "monotonicity of capQ is NOT checked",
           "N": N, "piHi": str(U), "bins": out}
    dst = Path(__file__).with_name("q0-degree3-binmax.json")
    dst.write_text(json.dumps(rep, indent=1) + "\n")
    print("PASS: 8 bins cover all", N + 1, "nodes; every capQ max at bin endpoint;",
          "min slack =", min(F(b["slack"]) for b in out))
    print("sha256 probe:", hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print("sha256 json :", hashlib.sha256(dst.read_bytes()).hexdigest())

if __name__ == "__main__":
    main()
