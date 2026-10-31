#!/usr/bin/env python3
"""Check the emitted B13 residual census for kernel-decide hygiene."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
PARTS = [f"EnergyTerminalResidualCensusC{i:02d}.lean" for i in range(1, 5)]
FORBIDDEN = ("sorry", "admit", "native_decide", "Lean.ofReduceBool", "implemented_by")


def main() -> int:
    result: dict[str, object] = {"parts": {}, "ok": True, "errors": []}
    total_blocks = 0
    for name in PARTS:
        path = LEAN / name
        raw = path.read_bytes()
        text = raw.decode("utf-8")
        blocks = text.count("decide +kernel +revert")
        bare = sum(
            line.count("decide +kernel") - line.count("decide +kernel +revert")
            for line in text.splitlines()
        )
        found = [token for token in FORBIDDEN if token in text]
        part_ok = (
            text.startswith("import N11Formalization.EnergyTerminalResidualCensusBase\n")
            and blocks > 0
            and bare == 0
            and not found
        )
        total_blocks += blocks
        result["parts"][name] = {
            "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest().upper(),
            "revert_blocks": blocks,
            "bare_kernel_decides": bare,
            "forbidden": found,
            "ok": part_ok,
        }
        result["ok"] = result["ok"] and part_ok
        if not part_ok:
            result["errors"].append(name)
    result["revert_blocks_total"] = total_blocks
    if total_blocks != 51:
        result["ok"] = False
        result["errors"].append(f"expected 51 revert blocks, found {total_blocks}")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
