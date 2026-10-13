"""make_localcopy.py -- build the modified copy of the read-only old kernel.

Member upper (next-cover-global). The original research-2026/lead/verify_c407_lead.py
is READ-ONLY for this member: it writes its output into the old directory.  This script
produces a byte-faithful copy under our own scope with exactly two changes:
  * SRC re-pointed to the same read-only asset (absolute path),
  * OUT redirected into members/upper/logs/,
plus a provenance header (original sha256 + input sha256 printed at run time).
No arithmetic, no candidate enumeration, no control is touched.
"""
import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]                      # .../ai4math2  (parents: upper,members,next-cover-global,research-2026,ai4math2)
ORIG = ROOT / 'research-2026/lead/verify_c407_lead.py'
DST = HERE / 'repro_c407_lead_localcopy.py'

src = ORIG.read_text(encoding='utf-8')

old = "ROOT = Path(__file__).resolve().parents[2]\n" \
      "SRC = ROOT / 'research-2026/session2/type14/out/hprec_sol.json'\n" \
      "OUT = Path(__file__).resolve().parent / 'c407_lead_result.txt'"
new = ("# --- MODIFIED COPY (member upper, next-cover-global) -----------------------------\n"
       "# Only this block differs from the read-only original (research-2026/lead/\n"
       "# verify_c407_lead.py): the asset is re-pointed by absolute path and OUT is\n"
       "# redirected into this member's logs/ (the original OUT dir is read-only to us).\n"
       "# All arithmetic / enumeration / controls below are byte-identical.\n"
       "HERE = Path(__file__).resolve().parent\n"
       "ROOT = HERE.parents[4]\n"
       "ORIG = ROOT / 'research-2026/lead/verify_c407_lead.py'\n"
       "SRC = ROOT / 'research-2026/session2/type14/out/hprec_sol.json'\n"
       "OUT = HERE.parent / 'logs' / 'c407_lead_result_localcopy.txt'")
assert old in src, 'anchor block not found'
out = src.replace(old, new)

anchor = "    say('== layer 0: ground-truth controls (known answers) ==')"
prov = ("    say('provenance: original kernel sha256 = '\n"
        "        + hashlib.sha256(ORIG.read_bytes()).hexdigest())\n"
        "    say('provenance: input hprec_sol sha256 = '\n"
        "        + hashlib.sha256(SRC.read_bytes()).hexdigest())\n" + anchor)
assert anchor in out
out = out.replace(anchor, prov, 1)
assert 'import json, math, sys' in out
out = out.replace('import json, math, sys', 'import hashlib, json, math, sys', 1)

DST.write_text(out, encoding='utf-8')
print('original  sha256', hashlib.sha256(ORIG.read_bytes()).hexdigest())
print('copy      sha256', hashlib.sha256(DST.read_bytes()).hexdigest())
print('changed lines:', sum(1 for a, b in zip(src.split('\n'), out.split('\n')) if a != b))
