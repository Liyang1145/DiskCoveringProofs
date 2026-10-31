#!/usr/bin/env python3
"""Replay every sector-bin step and bind the witnesses to the Lean table.

This independently recomputes the exact rational sector values, checks the
increase-then-decrease shape on all 18,369 within-bin adjacent steps, checks
all 63 inter-bin jumps, and requires the Lean `sectorBinWitness` table to match
the first exact argmax in each bin.  This is arithmetic evidence, not proof.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import probe_q0_degree3_nodes as probe  # noqa: E402

REPORT = HERE / "q0-degree3-piecewise-8.json"
LEAN = (HERE.parents[2] / "lean" / "N11Formalization" /
        "SevenClassQ0Deg3SectorBinWitness.lean")
OUT = HERE / "q0-degree3-sector-bin-lean-audit.json"


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def lean_witnesses() -> list[list[int]]:
    text = LEAN.read_text()
    block = text.split("def sectorBinWitness", 1)[1].split("theorem", 1)[0]
    rows = re.findall(r"^\s*!\[([^\]]+)\]\]?,?\s*$", block, re.MULTILINE)
    require(len(rows) == 9, f"parsed {len(rows)} Lean witness rows, expected 9")
    table = [[int(value.strip()) for value in row.split(",")] for row in rows]
    require(all(len(row) == 8 for row in table), "Lean witness row has wrong width")
    return table


def main() -> None:
    raw, row = probe.load()
    report = json.loads(REPORT.read_text())
    table = lean_witnesses()
    require(report["source_sha256"] == hashlib.sha256(raw).hexdigest(),
            "piecewise report source hash mismatch")

    mu = [probe.mid(x) for x in row["mu"]]
    lam = probe.mid(row["lambda"])
    _, upper = probe.interval(row["pi_interval"])
    qs = [upper * k / probe.N for k in range(probe.N + 1)]
    sines = [probe.sinHi(q) for q in qs]
    node8 = [F(item["node"]) for item in report["bins"]]
    segment = [(2 * a - probe.sinLo(2 * a)) / 2 for a in node8]

    total_steps = 0
    total_inc = 0
    total_dec = 0
    jump_rows = []
    bins = []
    for site, expected in enumerate(report["sectors"]):
        i = expected["site"]
        values = [
            segment[min(7, 8 * k // probe.N)] +
            probe.R2 * sines[k] / 2 +
            2 * lam * node8[min(7, 8 * k // probe.N)] - mu[i] * qs[k]
            for k in range(probe.N + 1)
        ]
        require(max(values) == F(expected["max"]),
                f"sector {i}: global maximum does not replay")

        row_bins = []
        edges = []
        for j in range(8):
            first = 256 * j
            last = 2048 if j == 7 else 256 * j + 255
            slice_ = values[first:last + 1]
            argmax = first + slice_.index(max(slice_))
            require(argmax == table[i][j],
                    f"sector {i} bin {j}: Lean witness {table[i][j]} != {argmax}")
            require(slice_.count(max(slice_)) == 1,
                    f"sector {i} bin {j}: argmax is not unique")

            signs = []
            for k in range(first, last):
                delta = values[k + 1] - values[k]
                require(delta != 0, f"sector {i} bin {j}: zero step at {k}")
                signs.append(1 if delta > 0 else -1)
            expected_steps = 255 if j < 7 else 256
            require(len(signs) == expected_steps,
                    f"sector {i} bin {j}: step count mismatch")
            require(all(signs[k] == 1 for k in range(argmax - first)),
                    f"sector {i} bin {j}: non-increasing step before argmax")
            require(all(signs[k] == -1 for k in range(argmax - first, expected_steps)),
                    f"sector {i} bin {j}: non-decreasing step after argmax")

            inc = argmax - first
            dec = last - argmax
            total_inc += inc
            total_dec += dec
            total_steps += len(signs)
            row_bins.append({
                "bin": j,
                "first": first,
                "last": last,
                "witness": argmax,
                "increasingSteps": inc,
                "decreasingSteps": dec,
            })
            if j < 7:
                jump = values[last + 1] - values[last]
                require(jump != 0,
                        f"sector {i} after bin {j}: zero inter-bin jump")
                edges.append({
                    "afterBin": j,
                    "k": last,
                    "delta": str(jump),
                    "direction": "up" if jump > 0 else "down",
                })
        bins.append({"site": i, "bins": row_bins})
        jump_rows.append({"site": i, "jumps": edges})

    require(total_steps == 9 * 2041 == 18369,
            "total within-bin step count mismatch")
    require(sum(len(row["jumps"]) for row in jump_rows) == 9 * 7 == 63,
            "inter-bin jump count mismatch")
    require(total_steps + 63 == 9 * 2048,
            "within-bin steps plus inter-bin jumps must cover every grid step")

    result = {
        "scope": "exact-rational replay and Lean-table binding; no Lean claim",
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "report_sha256": hashlib.sha256(REPORT.read_bytes()).hexdigest(),
        "lean_sha256": hashlib.sha256(LEAN.read_bytes()).hexdigest(),
        "withinBinAdjacentSteps": total_steps,
        "increasingSteps": total_inc,
        "decreasingSteps": total_dec,
        "interBinJumps": sum(len(row["jumps"]) for row in jump_rows),
        "bins": bins,
        "jumps": jump_rows,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: 72/72 Lean witnesses equal the exact unique bin argmax")
    print(f"PASS: {total_steps} within-bin steps ({total_inc} up, {total_dec} down)")
    print("PASS: 63/63 inter-bin jumps replayed")
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
