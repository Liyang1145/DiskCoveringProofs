# SPDX-License-Identifier: MIT
"""One-command mathematical checks, with explicit proof scope and fresh results."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("order", choices=("n11", "n12"))
    parser.add_argument("--quick", action="store_true", help="n12: check two atoms, never full replay")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--require-global", action="store_true", help="fail if the unrestricted global proof is not fully replayed")
    args = parser.parse_args(argv)
    try:
        if args.order == "n11":
            from mathcheck_n11 import run_checks
            result = run_checks(progress=lambda message: print(message, flush=True))
            global_replayed = result["full_global_proof_replayed"]
            marker = "N11 SCOPED MATH CHECK PASSED"
        else:
            from mathcheck_n12 import run_checks
            result = run_checks(workers=args.workers, limit=2 if args.quick else None)
            global_replayed = result["global_optimality_reproved"]
            marker = "N12 FULL K10 MATH REPLAY PASSED" if result["full_k10_arithmetic"] else "N12 SAMPLED MATH CHECK PASSED (NOT FULL)"
        result["checker_sha256"] = {p.name: sha(p) for p in (ROOT/"tools").glob("*math*.py")}
        result["input_sha256"] = {str(p.relative_to(ROOT)): sha(p) for p in (ROOT/"math_data"/args.order).iterdir() if p.is_file()}
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
        if args.require_global and not global_replayed:
            raise ValueError("Unrestricted global proof is not fully replayed by this checker; bounded arithmetic results do not satisfy --require-global.")
        print(marker)
        print("The analytic unrestricted global proof is outside this execution scope.")
        print(json.dumps({k: v for k, v in result.items() if k not in ("atomic_results", "input_sha256", "checker_sha256")}, indent=2))
        return 0
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, ImportError) as error:
        print(f"MATH CHECK FAILED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
