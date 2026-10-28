"""Insert the 23 batch root imports into lean\\N11Formalization.lean.

Placed immediately after the existing C450Source13Segment pilot block, before the
ActualHubEssentiality block. Only ONE import line per segment module; the transitive
closure pulls the Data + 32 grouped modules of every segment.

NOTE: C450Source13Segment is ALREADY imported (task-8 pilot). We add 14..36.
The final module (C450Source36Segment) is the one whose own RemainingSourceObligation
is vacuous, closing the chain.

Idempotent-ish: refuses to run if the block marker already exists.
Backs up to N11Formalization.lean.pre-batch-<date> before writing.
"""
from pathlib import Path
import hashlib
import re
import sys

W = Path(r"E:\ai4math2\research-2026\n11-formalization")
root = W / "lean" / "N11Formalization.lean"
backup = W / "lean" / "N11Formalization.lean.pre-batch-20261014"

MARK = "-- C450 BATCH ROOT INTEGRATION (task-9"
text = root.read_text(encoding="utf-8")
if MARK in text:
    print("MARKER ALREADY PRESENT: refusing to edit twice")
    sys.exit(1)

pre = hashlib.sha256(root.read_bytes()).hexdigest().upper()
anchor = "import N11Formalization.C450Source13Segment\n"
if anchor not in text:
    print("ANCHOR MISSING: C450Source13Segment import not found")
    sys.exit(1)

# modules to add: 14..36 (13 is the pilot's)
added = [f"import N11Formalization.C450Source{n}Segment" for n in range(14, 37)]
assert added[-1] == "import N11Formalization.C450Source36Segment"
assert len(added) == 23

block = ["",
         "-- C450 BATCH ROOT INTEGRATION (task-9, m6-c450-pilot, 2026-10-14).",
         "-- Completes the chain c450Segs[13..35] (23 emitted segments). With the",
         "-- pilot's C450Source13Segment this covers c450Segs[12..35], so",
         "-- C450Source11Segment.RemainingSourceObligation (the root's h450,",
         "-- ActualMetricClassReduction.lean:65) is obtainable from the chain.",
         "-- The LAST module C450Source36Segment has remainingSegs = c450Segs.drop 36",
         "-- = [], so ITS OWN RemainingSourceObligation is vacuous; but its",
         "-- predecessor c450Segs.drop 35 is a singleton, so C450Source36Segment",
         "-- still supplies its own source36_paid (kernel-checked).",
         "-- One import line per segment: the transitive closure pulls Data + 32",
         "-- grouped modules for each.",
         *added, ""]

if not backup.exists():
    backup.write_bytes(root.read_bytes())
    print(f"backup written: {backup.name}")

new = text.replace(anchor, anchor + "\n".join(block), 1)
root.write_text(new, encoding="utf-8", newline="\n")
post = hashlib.sha256(root.read_bytes()).hexdigest().upper()

# structural verification
chk = root.read_text(encoding="utf-8")
missing = [a for a in added if a not in chk]
print(f"pre  sha256: {pre}")
print(f"post sha256: {post}")
print(f"added lines: {len(block)}  imports added: {len(added)}")
print(f"all 23 imports present: {not missing}")
n13 = len(re.findall(r"^import N11Formalization\.C450Source13Segment$", chk, re.M))
n36 = len(re.findall(r"^import N11Formalization\.C450Source36Segment$", chk, re.M))
print(f"C450Source13Segment import count (want 1): {n13}")
print(f"C450Source36Segment import count (want 1): {n36}")
sys.exit(0 if not missing and n13 == 1 and n36 == 1 else 1)
