"""Extract the exact already-tested ear enumeration into a stdlib-only module."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    original = ROOT / "probe_zero_budget_ear_covers.py"
    target, reportpath = ROOT / "zero_budget_ear_kernel.py", ROOT / "zero-budget-ear-kernel-derivation.json"
    assert not target.exists() and not reportpath.exists()
    text = original.read_text(encoding="utf8")
    start, end = text.index("def ear_branches("), text.index("\ndef experiment(")
    function = text[start:end]
    preamble = '''"""Stdlib-only necessary zero-budget ear-cover enumeration."""
from pathlib import Path
from itertools import combinations, product
import sys
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from complete_simple_collar import simple_holes, bits
assert __debug__


'''
    target.write_text(preamble+function, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "verified_mechanical_extraction": True, "original_source_sha256": sha(original),
        "derived_source_sha256": sha(target), "source_sha256": sha(Path(__file__)),
        "exact_function_text": function, "preamble": preamble,
        "no_optimizer_imported_by_extracted_kernel": True, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
