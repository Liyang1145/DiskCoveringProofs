#!/usr/bin/env python3
"""Independent static verifier for the lane-C CensusC01..C04 split modules.

Scope: source-level structure only (NOT elaboration, NOT kernel credit).
Checks:
  * per-index theorems mem_iff_id_<id> tile 0..5010 exactly once (no dup/gap);
  * each block lemma mem_iff_blockNN has interval [100*NN, min(100*NN+100,5011))
    and its bullets reference exactly the ids of that interval;
  * the consumer EnergyTerminalResidualCensus.lean calls mem_iff_block00..50;
  * forbidden-token scan (sorry/admit/axiom/native_decide/ofReduceBool/
    implemented_by/maxHeartbeats).
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
LEAN = ROOT / "lean/N11Formalization"
FILES = [LEAN / f"EnergyTerminalResidualCensusC0{i}.lean" for i in (1, 2, 3, 4)]
CONSUMER = LEAN / "EnergyTerminalResidualCensus.lean"
N = 5011

FORBIDDEN = ["sorry", "admit", "axiom", "native_decide", "ofReduceBool",
             "implemented_by", "maxHeartbeats"]

errors = []

# ---- per-index theorems ----
id_re = re.compile(r"^theorem mem_iff_id_(\d{4}) \(n : Fin 5011\) \(hn : n\.val = (\d+)\)", re.M)
seen = {}
for f in FILES:
    text = f.read_text()
    for name, val in id_re.findall(text):
        if int(name) != int(val):
            errors.append(f"{f.name}: theorem id {name} claims n.val = {val}")
        if name in seen:
            errors.append(f"{f.name}: duplicate id {name} (also {seen[name]})")
        seen[name] = f.name
missing = [f"{i:04d}" for i in range(N) if f"{i:04d}" not in seen]
if missing:
    errors.append(f"missing {len(missing)} ids, first={missing[:5]}")

# ---- block lemmas ----
blk_hdr = re.compile(
    r"^theorem mem_iff_block(\d{2}) \(n : Fin 5011\) \(hlo : (\d+) ≤ n\.val\) \(hhi : n\.val < (\d+)\)",
    re.M)
blk_bullet = re.compile(r"exact mem_iff_id_(\d{4}) _ rfl")
blocks = {}
for f in FILES:
    text = f.read_text()
    for idx, lo, hi in blk_hdr.findall(text):
        blocks[int(idx)] = (int(lo), int(hi), f.name)
    # bullets between headers
    parts = re.split(r"(?=^theorem mem_iff_block)", text, flags=re.M)
    for p in parts:
        m = blk_hdr.search(p)
        if not m:
            continue
        idx, lo, hi = int(m.group(1)), int(m.group(2)), int(m.group(3))
        want = list(range(lo, hi))
        got = [int(x) for x in blk_bullet.findall(p)]
        if got != want:
            errors.append(f"{f.name}: block{idx:02d} bullets != [{lo},{hi}) "
                          f"(len {len(got)} vs {len(want)})")

expected = {b: (100 * b, min(100 * b + 100, N)) for b in range(51)}
if set(blocks) != set(expected):
    errors.append(f"block ids mismatch: got {sorted(blocks)} vs 0..50")
for b, (lo, hi, _) in blocks.items():
    if (lo, hi) != expected.get(b):
        errors.append(f"block{b:02d} interval ({lo},{hi}) != {expected.get(b)}")

# ---- consumer interface ----
cons = CONSUMER.read_text()
for b in range(51):
    pat = re.compile(rf"\bmem_iff_block{b:02d}\b")
    cnt = len(pat.findall(cons))
    if cnt != 1:
        errors.append(f"consumer references mem_iff_block{b:02d} {cnt} times (want 1)")

# ---- forbidden tokens ----
for f in FILES + [CONSUMER]:
    kept = [ln for ln in f.read_text().splitlines()
            if not ln.lstrip().startswith("#print")]
    text = chr(10).join(kept)
    for tok in FORBIDDEN:
        pat = re.compile(r"\baxiom\b") if tok == "axiom" else re.compile(re.escape(tok))
        if pat.search(text):
            errors.append(f"forbidden token {tok!r} in {f.name}")

if errors:
    print("FAIL")
    for e in errors[:40]:
        print("  -", e)
    sys.exit(1)
print(f"PASS  per-index ids: {len(seen)} (0..{N-1}); blocks: {len(blocks)}; "
      f"consumer: 51 calls; forbidden tokens: none")
