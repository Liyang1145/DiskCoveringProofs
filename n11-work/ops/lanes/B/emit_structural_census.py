#!/usr/bin/env python3
"""Emit the lane-B-owned 373-id refined residual census."""
from __future__ import annotations
import hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
LEAN=ROOT/'n11-work/lean/N11Formalization'; EVIDENCE=ROOT/'n11-work/evidence-20261028/evidence'
OUT=LEAN/'EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.lean'
REMOVED={37,2337,2341,2965,3040,3112,3116,3431,3440,3573,3589,3623,3633,3777,3792,3853}
def node_ids(module):
 text=(LEAN/f'{module}.lean').read_text(encoding='utf-8')
 m=re.search(r'^def nodeID\s*:\s*Case\s*→\s*Fin\s*5011\s*:=\s*!\[([^\]]+)\]',text,re.M)
 if m is None: raise SystemExit(f'missing nodeID array in {module}')
 return {int(x) for x in re.findall(r'\d+',m.group(1))}
def terminal_ids():
 text=(LEAN/'DBMSourceTreeData.lean').read_text(encoding='utf-8')
 pat=re.compile(r'def node(\d+) : Node 5011 where(.*?)(?=\ndef node\d+ : Node 5011 where|\ndef data)',re.S)
 return {int(m.group(1)) for m in pat.finditer(text) if 'terminal := true' in m.group(2)}
def patch_ids():
 text=(LEAN/'Patch120DomainPacket.lean').read_text(encoding='utf-8')
 m=re.search(r'^def patchID\s*:\s*Fin\s*120\s*→\s*Fin\s*5011\s*:=\s*!\[([^\]]+)\]',text,re.M)
 if m is None: raise SystemExit('missing patchID array')
 return {int(x) for x in re.findall(r'\d+',m.group(1))}
components={name:node_ids(mod) for name,mod in {'lambda7':'Lambda0Batch7Packet','tangent':'Lambda0TangentChordC01Packet','cutting':'CuttingPlaneBatch7Packet','batch22':'Paid16Batch22Packet',**{f'G{i:02}':f'Paid16GeneralG{i:02}' for i in range(1,13)}}.items()}
b11={284,562,4348,984,1112,2166,2162,3436,4179,4265,4267}|components['lambda7']|components['tangent']|components['cutting']|components['batch22']|set().union(*(components[f'G{i:02}'] for i in range(1,13)))
next505=set()
for m in re.finditer(r'^def ids(\d\d) : Finset \(Fin 5011\) := \{([^}]*)\}',(LEAN/'Paid16GeneralNext505.lean').read_text(encoding='utf-8'),re.M): next505|={int(x) for x in re.findall(r'\d+',m.group(2))}
rest=set(json.loads((EVIDENCE/'rest1182-emission-manifest.json').read_text(encoding='utf-8-sig'))['ids'])
terminals=terminal_ids(); sharp=patch_ids(); b12=b11|next505; b13=b12|rest
r389=terminals-sharp-b13; r373=r389-REMOVED
assert (len(b11),len(b12),len(b13))==(310,815,1997)
assert (len(terminals),len(sharp),len(r389),len(r373))==(2506,120,389,373)
assert REMOVED<=r389
# Independent cross-check against the frozen, checked-in 389-id chunk definitions.
base_text=(LEAN/'EnergyTerminalResidualCensusBase.lean').read_text(encoding='utf-8')
base389=set()
for m in re.finditer(r'^def chunk\d+ : Finset \(Fin 5011\) := \{([^}]*)\}',base_text,re.M):
    base389 |= {int(x) for x in re.findall(r'\d+',m.group(1))}
assert len(base389)==389 and base389-REMOVED==r373
ids=sorted(r373); chunks=[ids[i:i+100] for i in range(0,len(ids),100)]
assert [len(c) for c in chunks]==[100,100,100,73]
BS=100; BC=(5011+BS-1)//BS
f=lambda v:'{'+','.join(map(str,v))+'}'
L=['''import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual

/-! Lane-B-owned literal census of the 373 ids left after the sixteen certified
refinements. Generated from terminal/packet sources and the rest1182 manifest;
block-local kernel checks only. Cardinality only; no residual radius is paid. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus
open Finset
noncomputable section''']
for i,c in enumerate(chunks):
 L += [f'def chunk{i} : Finset (Fin 5011) := {f(c)}',f'theorem chunk{i}_card : chunk{i}.card = {len(c)} := by decide +kernel']
L.append('def residual373 : Finset (Fin 5011) := chunk0 ∪ (chunk1 ∪ (chunk2 ∪ chunk3))')
for i in range(4):
 for j in range(i+1,4): L.append(f'private theorem chunk{i}_disjoint_chunk{j} : Disjoint chunk{i} chunk{j} := by decide +kernel')
L += ['private theorem chunk0_disjoint : Disjoint chunk0 (chunk1 ∪ (chunk2 ∪ chunk3)) := by','  rw [Finset.disjoint_union_right]','  exact ⟨chunk0_disjoint_chunk1, by','    rw [Finset.disjoint_union_right]','    exact ⟨chunk0_disjoint_chunk2, chunk0_disjoint_chunk3⟩⟩','private theorem chunk1_disjoint : Disjoint chunk1 (chunk2 ∪ chunk3) := by','  rw [Finset.disjoint_union_right]','  exact ⟨chunk1_disjoint_chunk2, chunk1_disjoint_chunk3⟩','private theorem chunk2_disjoint : Disjoint chunk2 chunk3 := chunk2_disjoint_chunk3','theorem residual373_card : residual373.card = 373 := by','  rw [residual373, Finset.card_union_of_disjoint chunk0_disjoint, chunk0_card]','  rw [Finset.card_union_of_disjoint chunk1_disjoint, chunk1_card]','  rw [Finset.card_union_of_disjoint chunk2_disjoint, chunk2_card]','  rw [chunk3_card]','  norm_num']
# Kernel decisions are limited to ten source indices.  The bounded block
# theorems then dispatch over those small facts; this avoids both a 100-index
# kernel term and open Fin variables surviving into `decide +kernel`.
P = ("n ∈ residual373 ↔\n"
     "      n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs")
SQ = "EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff"

def sub(j: int) -> str:
    lo = 10 * j
    if j < 501:
        bounds = f"(hlo : {lo} ≤ n.val) (hhi : n.val < {lo + 10})"
    else:
        bounds = "(hlo : 5010 ≤ n.val) (hhi : n.val < 5011)"
    return f"""private theorem mem_sub_{j:03d} (n : Fin 5011)
    {bounds} :
    {P} := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    change ((⟨k, by decide⟩ : Fin 5011) ∈ residual373 ↔
      (⟨k, by decide⟩ : Fin 5011) ∈
        EnergyTerminalBatchB13RefineSixteenResidual.residualIDs) <;>
    rw [{SQ}] <;> decide +kernel

"""

for j in range(502):
    L.append(sub(j).rstrip())
for i in range(50):
    lo = 10 * i
    ranges = [f"({lo + 10*r} ≤ n.val ∧ n.val < {lo + 10*r + 10})"
              for r in range(1, 10)]
    cover = f"n.val < {lo + 10} ∨ " + " ∨ ".join(ranges)
    pats = " | ".join(f"h{r}" for r in range(10))
    L += [f"private theorem mem_iff_block{i:02d} (n : Fin 5011)",
          f"    (hlo : {lo} ≤ n.val) (hhi : n.val < {lo + 100}) :",
          f"    {P} := by", f"  have hcover : {cover} := by omega",
          f"  rcases hcover with {pats}",
          f"  · exact mem_sub_{10*i:03d} n hlo h0"]
    L += [f"  · exact mem_sub_{10*i+r:03d} n h{r}.1 h{r}.2" for r in range(1, 10)]
    L.append("")
L += ['private theorem mem_iff_block50 (n : Fin 5011) (hlo : 5000 ≤ n.val) :',
      f'    {P} := by', '  have hcases : n.val < 5010 ∨ n.val = 5010 := by omega',
      '  rcases hcases with h0 | h1', '  · exact mem_sub_500 n hlo h0',
      '  · exact mem_sub_501 n (by omega) n.isLt', '']
L += ['theorem residualIDs_eq_residual373 :','    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs = residual373 := by','  ext n']
cover=['n.val < 100']+[f'({i*100} ≤ n.val ∧ n.val < {(i+1)*100})' for i in range(1,50)]+['5000 ≤ n.val']
L += ['  have hcover : '+' ∨ '.join(cover)+' := by omega','  rcases hcover with '+' | '.join(f'h{i}' for i in range(51))]
for i in range(51):
 proof=f'mem_iff_block00 n (Nat.zero_le _) h0' if i==0 else (f'mem_iff_block50 n h50' if i==50 else f'mem_iff_block{i:02d} n h{i}.1 h{i}.2')
 L.append(f'  · exact ({proof}).symm')
L += ['theorem residualIDs_card :','    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs.card = 373 := by','  rw [residualIDs_eq_residual373, residual373_card]','end','end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus','#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.residual373_card','#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.residualIDs_eq_residual373','#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.residualIDs_card','#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.residualIDs_card']
OUT.write_text('\n'.join(L)+'\n',encoding='utf-8')
h=lambda path: hashlib.sha256(path.read_bytes()).hexdigest().upper()
REPORT=HERE/'emit_structural_census-report.json'
payload={'scope':'deterministic source reconstruction, frozen-census cross-check, and static target audit only; not a Lean kernel check and pays no radius',
 'counts':{'terminal':len(terminals),'sharp':len(sharp),'unconditional_residual':len(r389),'removed_certified':len(REMOVED),'refined_residual':len(ids)},
 'chunks':[len(c) for c in chunks],
 'sha256':{str(OUT.relative_to(ROOT)):h(OUT),str((LEAN/'EnergyTerminalBatchB13RefineSixteenResidualStructural.lean').relative_to(ROOT)):h(LEAN/'EnergyTerminalBatchB13RefineSixteenResidualStructural.lean'),str(Path(__file__).resolve().relative_to(ROOT)):h(Path(__file__).resolve())}}
REPORT.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps({'output':str(OUT.relative_to(ROOT)),'count':len(ids),'chunks':[len(c) for c in chunks],'base389_crosscheck':True},sort_keys=True))
