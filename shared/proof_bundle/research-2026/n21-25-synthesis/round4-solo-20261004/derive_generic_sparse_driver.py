"""Keep the production acceptance body; parameterize B and new control paths."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    target = ROOT / "run_family_sparse_collar.py"
    reportpath = ROOT / "generic-sparse-driver-derivation.json"
    assert not target.exists() and not reportpath.exists()
    source = ROOT / "run_sparse_collar_flexible.py"
    full = source.read_text(encoding="utf8")
    body = full[full.index("def main():"):]
    new = re.sub(r"\b14\b", "B", body)
    new = new.replace('"25", "B", relative', '"25", str(B), relative')
    new = new.replace(
        "    args = ap.parse_args()\n",
        '    args = ap.parse_args()\n    B = read(args.library)["B"]\n    assert B == 15\n', 1)
    new = new.replace('"test_sparse_collar_flexible.py"', '"test_generic_sparse_collar.py"')
    new = new.replace("N25/B14", "N25/B15")
    new = new.replace('    output.mkdir(parents=True)\n',
                      '    for extra in ("family_sparse_gate.py", "derive_generic_sparse_driver.py",\n'
                      '                  "generic-sparse-driver-derivation.json"):\n'
                      '        bind(files, ROOT / extra)\n'
                      '    output.mkdir(parents=True)\n', 1)
    preamble = '''"""Derived generic-B strict collar production driver; no old inputs edited."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import os
import re
import subprocess
import sys
import threading
import time
ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2].resolve()
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import validate
from test_outer_collar import linux_path, WSL, collar_codes
from test_sparse_collar import mechanical_derivation
from n25_outer_search import read, publish, bind, unchanged
from family_sparse_gate import sparse_library_gate
assert __debug__

'''
    target.write_text(preamble+new, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "source_driver_sha256": sha(source), "derived_driver_sha256": sha(target),
        "original_acceptance_body_sha256": hashlib.sha256(body.encode()).hexdigest(),
        "same_native_source_and_recursion_used": True,
        "boundary_parameter_and_new_control_source_paths_only": True,
        "extra_generic_gate_files_bound": True, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
