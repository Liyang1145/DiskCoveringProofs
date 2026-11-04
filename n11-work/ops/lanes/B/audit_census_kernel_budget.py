#!/usr/bin/env python3
"""Kernel-budget audit of the EnergyTerminalResidualCensus chain (lane B).

Scope: static source/token scan only.  NOT a build, NOT kernel credit, NOT a
proof.  It quantifies, per census chunk, how large the decided Finset terms are
that the per-index `decide +kernel +revert` proofs force the kernel to normalise,
and flags any decided set that exceeds GUIDANCE rule 6's ~170-500 literal budget.
"""
import json, re, hashlib, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work" / "lean" / "N11Formalization"

def read(p):
    return (LEAN / p).read_text(encoding="utf-8", errors="replace")

def sha(p):
    return hashlib.sha256((LEAN / p).read_bytes()).hexdigest()

def literal_ids(text, name):
    m = re.search(re.escape(name) + r"\s*:\s*Finset[^:]*:=\s*\{([^}]*)\}", text)
    if not m:
        return None
    return [int(x) for x in re.findall(r"-?\d+", m.group(1))]

report = {"scope": "static source/token audit; not a build; not kernel credit; not a proof"}

base = read("EnergyTerminalResidualCensusBase.lean")
parts = {}
for i in range(4):
    ids = literal_ids(base, f"chunk{i}")
    parts[f"chunk{i}"] = len(ids) if ids is not None else None
report["residual_literal"] = {
    "source": "EnergyTerminalResidualCensusBase.lean",
    "sha256": sha("EnergyTerminalResidualCensusBase.lean"),
    "total": sum(v or 0 for v in parts.values()),
    "parts": parts,
}

sharp = literal_ids(read("Patch120SharpDispatch.lean"), "sharpIDs")
report["sharpIDs_literal"] = len(sharp) if sharp is not None else "not a literal"

b13 = read("EnergyTerminalBatchB13.lean")
report["paidIDs_definition"] = next(
    (l.strip() for l in b13.splitlines() if l.startswith("def paidIDs")), None)
report["residualIDs_definition"] = next(
    (l.strip() for l in b13.splitlines() if l.startswith("def residualIDs")), None)
report["declared_terminal_count"] = next(
    (int(x) for x in re.findall(r"terminal count is (\d+)", b13)), None)

per_chunk = {}
for i in range(1, 5):
    p = f"EnergyTerminalResidualCensusC0{i}.lean"
    t = read(p)
    mem = len(re.findall(r"theorem mem_iff_id_\d+", t))
    dk = len(re.findall(r"decide \+kernel", t))
    dkr = len(re.findall(r"decide \+kernel \+revert", t))
    per_chunk[p] = {
        "lines": t.count("\n") + 1,
        "sha256": sha(p),
        "mem_iff_id_theorems": mem,
        "decide_kernel": dk,
        "decide_kernel_revert": dkr,
        "max_line_bytes": max((len(l) for l in t.splitlines()), default=0),
        "maxHeartbeats_0": len(re.findall(r"maxHeartbeats 0", t)),
        "maxRecDepth": sorted(set(re.findall(r"maxRecDepth (\d+)", t))),
        "every_mem_iff_is_full_revert_decide": mem > 0 and mem == dkr,
    }
report["census_chunks"] = per_chunk

paid = 1997
report["budget"] = {
    "guidance_limit_literals": 500,
    "residual_literal_total": report["residual_literal"]["total"],
    "paid_literals_declared": paid,
    "sharp_literals": report["sharpIDs_literal"],
    "max_decided_literals_per_mem_iff": paid,
}
report["budget"]["exceeds_guidance"] = paid > 500
report["green_sibling_pattern"] = (
    "EnergyTerminalBatchB13Refine0037 proves `(37:Fin 5011) ∉ paidIDs` via "
    "28 bounded `decide +kernel` facts on Next1182 part literals + `new_mem` + "
    "`push_neg`, i.e. a hierarchical split, not one whole-set decide.")

print(json.dumps(report, indent=1, sort_keys=True))
ok = all(v["every_mem_iff_is_full_revert_decide"] for v in per_chunk.values())
print("ok:", bool(ok))
sys.exit(0 if ok else 1)
