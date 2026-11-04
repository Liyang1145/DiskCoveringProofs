#!/usr/bin/env python3
"""Lane-B census repair cost (static source scan; no Lean build, no kernel credit)."""
from pathlib import Path
import hashlib, json, re

LANE = Path(__file__).resolve().parent
LEAN = LANE.parents[3] / "n11-work/lean/N11Formalization"
_c = {}

def text(m):
    if m not in _c:
        _c[m] = (LEAN / f"{m}.lean").read_text(encoding="utf-8")
    return _c[m]

def rhs_of(m, name):
    mm = re.search(rf"^def {name}\b[^:]*:\s*Finset \(Fin 5011\)\s*:=\s*(.*?)(?=^\S)",
                   text(m), re.MULTILINE | re.DOTALL)
    assert mm, (m, name)
    return mm.group(1)

def _vector(m, name):
    mm = re.search(rf"^def {name}\b[^=]*:=\s*!\[(.*?)\]", text(m), re.MULTILINE | re.DOTALL)
    assert mm, (m, name)
    return {int(x) for x in re.findall(r"\d+", mm.group(1))}

def resolve(m, name):
    r = rhs_of(m, name)
    out = set()
    if "{" in r and "}" in r:
        out |= {int(x) for x in re.findall(r"\d+", r[r.index("{") + 1:r.rindex("}")])}
    out |= {int(x) for x in re.findall(r"insert (\d+) ", r)}
    if "image patchID" in r:
        out |= _vector("Patch120DomainPacket", "patchID")
    for mod, nm in re.findall(r"([A-Z][A-Za-z0-9_]*)\.([A-Za-z0-9_]+)", r):
        if mod in ("Finset", "Fin") or not (LEAN / f"{mod}.lean").exists():
            continue
        try:
            out |= resolve(mod, nm)
        except AssertionError:
            continue
    return out

B09 = resolve("EnergyTerminalBatchB09", "paidIDs")
F42 = resolve("Paid16GeneralFirst42", "newIDs")
R210 = resolve("Paid16GeneralRemaining210", "newIDs")
N505 = [resolve("Paid16GeneralNext505", f"ids{i:02d}") for i in range(25)]
def _s_ids(s):
    m = f"Paid16GeneralNext1182S{s:02d}"
    names = sorted(set(re.findall(r"^def (ids\d+)\b", text(m), re.MULTILINE)))
    return [resolve(m, nm) for nm in names]

N1182 = [_s_ids(s) for s in range(1, 9)]
sharp = resolve("Patch120SharpDispatch", "sharpIDs")
census = set().union(*[resolve("EnergyTerminalResidualCensusBase", f"chunk{i}") for i in range(4)])
b10 = B09 | F42
paid = b10 | R210 | set().union(*N505) | set().union(*[set().union(*p) for p in N1182])
assert len(paid) == 1997 and len(sharp) == 120 and len(census) == 389, (len(paid), len(sharp), len(census), len(b10), len(R210), len(set().union(*N505)), len(set().union(*[set().union(*p) for p in N1182])))
assert not (census & paid) and not (census & sharp)
flat = [len(y) for p in N1182 for y in p]
n505s = [len(x) for x in N505]
report = {
  "paid_count": len(paid), "sharp_count": len(sharp), "census_count": len(census),
  "census_disjoint_paid": True, "census_disjoint_sharp": True,
  "leaf_sizes": {"B10_total": len(b10), "Remaining210": len(R210),
                 "Next505_parts": n505s, "Next1182_parts": flat, "sharp": len(sharp)},
  "max_leaf_literals": max([len(b10), len(R210)] + n505s + flat),
  "leaf_decides_per_index_notpaid": 2 + len(n505s) + len(flat),
  "naive_decide_literals_per_index": len(paid),
  "guidance_limit": 500,
  "scope": "static source scan; not a build, not kernel credit",
}
(LANE / "audit_census_fix_cost-report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, indent=2))
print("script sha256", hashlib.sha256(Path(__file__).read_bytes()).hexdigest().upper())
