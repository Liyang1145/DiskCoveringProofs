"""Emit core-Lean replays of the generated switch trees (and the A25 batch switch0 as positive control).
Class33Core/SwTrees/<Tab>S<j>.lean : coefficients taken FROM the table module (Rep1.table / Q0M2.table),
leaves chunked, each chunk checked by decide +kernel; global tiling checked from chunk endpoints."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N11
import json,sys,os,re
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent; OUT=ROOT/'lean-core'/'Class33Core'/'SwTrees'; OUT.mkdir(parents=True,exist_ok=True)
def q(x): x=F(x); return f'({x.numerator}/{x.denominator} : Rat)' if x.denominator!=1 else f'({x.numerator} : Rat)'
CH=int(os.environ.get('CHUNK','60'))
PART=int(os.environ.get('PART','780'))
def wr(p,s):
  t=str(p)+'.tmp'; open(t,'w').write(s); os.replace(t,p)
def emit(name, imports, coeff_expr, M, leaves, note):
  L=[(F(a),F(b)) for a,b in leaves]; parts=[L[i:i+PART] for i in range(0,len(L),PART)]
  head=f"{imports}\nimport Class33Core.SwitchKernel\n"
  base=f"{head}/- {note}\n   coefficients/bound. Core-Lean pre-validation, NOT credit. -/\nnamespace Class33Core.SwTrees.{name}\nopen Class33Core Class33Core.SwitchKernel\ndef coeff : Coeff := {coeff_expr}\ndef M : Rat := {q(M)}\nend Class33Core.SwTrees.{name}\n"
  wr(OUT/f'{name}Base.lean',base)
  mods=[f'{name}Base']
  pends=[]
  for k,P in enumerate(parts):
    ch=[P[i:i+CH] for i in range(0,len(P),CH)]
    s=f"import Class33Core.SwTrees.{name}Base\nnamespace Class33Core.SwTrees.{name}.P{k}\nopen Class33Core Class33Core.SwitchKernel Class33Core.SwTrees.{name}\n"
    for i,c in enumerate(ch):
      s+=f"def c{i} : List (Rat × Rat) := [{','.join(f'({q(a)},{q(b)})' for a,b in c)}]\n"
      s+=f"theorem c{i}_ok : allLeavesOK coeff M c{i} = true ∧ chainB c{i} = true := by decide +kernel\n"
    ends=[(c[0][0],c[-1][1]) for c in ch]
    s+=f"def ends : List (Rat × Rat) := [{','.join(f'({q(a)},{q(b)})' for a,b in ends)}]\n"
    s+=f"theorem ends_ok : chainB ends = true ∧ [{','.join(f'(c{i}.head?.map (·.1), c{i}.getLast?.map (·.2))' for i in range(len(ch)))}] = ends.map (fun x => (some x.1, some x.2)) := by decide +kernel\n"
    s+=f"end Class33Core.SwTrees.{name}.P{k}\n"
    wr(OUT/f'{name}P{k}.lean',s); mods.append(f'{name}P{k}'); pends.append((P[0][0],P[-1][1]))
  agg="".join(f"import Class33Core.SwTrees.{name}P{k}\n" for k in range(len(parts)))
  agg+=f"/- {note}\n   {len(L)} leaves in {len(parts)} parts. Core-Lean pre-validation, NOT credit. -/\nnamespace Class33Core.SwTrees.{name}\nopen Class33Core.SwitchKernel\n"
  agg+=f"def partEnds : List (Rat × Rat) := [{','.join(f'({q(a)},{q(b)})' for a,b in pends)}]\n"
  agg+=f"theorem parts_match : [{','.join(f'(P{k}.ends.head?.map (·.1), P{k}.ends.getLast?.map (·.2))' for k in range(len(parts)))}] = partEnds.map (fun x => (some x.1, some x.2)) := by decide +kernel\n"
  agg+=f"/-- all leaves accepted (part theorems) and they tile [0,1571/1000]. -/\ntheorem tiles : chainB partEnds = true ∧ (partEnds.head?.map (·.1)) = some 0 ∧ (partEnds.getLast?.map (·.2)) = some (1571/1000) := by decide +kernel\n"
  agg+=f"end Class33Core.SwTrees.{name}\n"
  wr(OUT/f'{name}.lean',agg); mods.append(name)
  return mods
if __name__=='__main__':
  # positive control: A25 batch switch0 leaves (Lean-green module)
  src=Path(DCP_N11+'/wip/lean/N11Formalization/SharedMomentConcreteSwitchBatch.lean').read_text()
  v={m.group(1):F(m.group(2).strip('()')) for m in re.finditer(r'def start0_switch0_(p|q|b|d2|d1|bound) : ℚ := \((.*?) : ℚ\)',src)}
  pat=re.compile(r'theorem start0_switch0_node_\d+ : Certificate start0_switch0_leaf\n    \(switchCell \((.*?) : ℚ\) \((.*?) : ℚ\)\) := by\n  apply Certificate.accept')
  lv=sorted((F(a),F(b)) for a,b in pat.findall(src))
  allm=[]
  allm+=emit('Control0','',f"⟨{q(v['p'])},{q(v['q'])},{q(v['b'])},{q(v['d2'])},{q(v['d1'])}⟩",v['bound'],[(str(a),str(b)) for a,b in lv],'POSITIVE CONTROL: A25 SharedMomentConcreteSwitchBatch start0_switch0 accepted leaves')
  for tab,mod in [('rep1','Rep1'),('q0m2','Q0M2')]:
    d=json.loads((ROOT/'data'/f'switch_trees_{tab}.json').read_text())
    for j in range(9):
      r=d[str(j)]
      allm+=emit(f'{mod}S{j}',f'import Class33Core.{mod}',f'⟨{mod}.table.switchP {j},{mod}.table.switchQ {j},{mod}.table.switchB {j},{mod}.table.switchD2 {j},{mod}.table.switchD1 {j}⟩',F(r['M']),r['leaves'],f'{tab} Lean switch {j}, M={r["M"]} (hist upper {r["hist_upper"]:.8f})')
  open(ROOT/'data'/'core_switch_modules.txt','w').write('\n'.join(allm)+'\n'); print(len(allm),'modules')
