#!/usr/bin/env python3
"""Independently reconstruct the terminal census and check the B13 partition count.

Scope is source parsing and exact finite-set arithmetic only; this is not a Lean
kernel check and does not pay any radius.
"""
from __future__ import annotations
import hashlib, json, re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
EVIDENCE = ROOT / "n11-work/evidence-20261028/evidence"
OUT = HERE / "audit_terminal_census-report.json"

def terminal_ids():
    text = (LEAN / "DBMSourceTreeData.lean").read_text(encoding="utf-8")
    pat = re.compile(r"def node(\d+) : Node 5011 where(.*?)(?=\ndef node\d+ : Node 5011 where|\ndef data)", re.S)
    return {int(m.group(1)) for m in pat.finditer(text) if "terminal := true" in m.group(2)}

def ids_from(module, regex):
    text = (LEAN / f"{module}.lean").read_text(encoding="utf-8")
    return {int(x) for m in re.finditer(regex, text, re.M) for x in re.findall(r"\d+", m.group(1))}

terminals = terminal_ids()
sharp_text = (LEAN / "Patch120DomainPacket.lean").read_text(encoding="utf-8")
m = re.search(r"^def patchID\s*:\s*Fin\s*120\s*→\s*Fin\s*5011\s*:=\s*!\[([^\]]+)\]", sharp_text, re.M)
sharp = {int(x) for x in re.findall(r"\d+", m.group(1))}
rest = set(json.loads((EVIDENCE / "rest1182-emission-manifest.json").read_text(encoding="utf-8-sig"))["ids"])
base_text = (LEAN / "EnergyTerminalResidualCensusBase.lean").read_text(encoding="utf-8")
residual389 = {int(x) for m in re.finditer(r"^def chunk\d+ : Finset \(Fin 5011\) := \{([^}]*)\}", base_text, re.M) for x in re.findall(r"\d+", m.group(1))}
removed = {37,2337,2341,2965,3040,3112,3116,3431,3440,3573,3589,3623,3633,3777,3792,3853}
b12 = (terminals - sharp - residual389) - rest
paid = b12 | rest
residual = residual389
assert (len(terminals), len(sharp), len(b12), len(rest), len(paid)) == (2506,120,815,1182,1997)
assert len(residual) == 389 and removed <= residual and len(residual - removed) == 373
assert terminals == sharp | paid | residual and not (sharp & paid or sharp & residual or paid & residual)
assert paid == b12 | rest
h = lambda p: hashlib.sha256(p.read_bytes()).hexdigest().upper()
report = {
  "ok": True,
  "scope": "independent source parsing and exact finite-set arithmetic; not a Lean kernel check",
  "counts": {"terminal":len(terminals),"sharp":len(sharp),"b12_paid":len(b12),"rest1182":len(rest),"b13_paid":len(paid),"residual389":len(residual),"refined_residual373":len(residual-removed)},
  "partition_exact": True,
  "sha256": {"audit":h(Path(__file__).resolve()),"DBMSourceTreeData.lean":h(LEAN/"DBMSourceTreeData.lean"),"rest1182-manifest":h(EVIDENCE/"rest1182-emission-manifest.json")},
}
OUT.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n", encoding="utf-8")
print(json.dumps(report, sort_keys=True))
