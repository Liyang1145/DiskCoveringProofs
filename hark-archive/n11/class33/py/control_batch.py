"""Positive control for switch_kernel.py: every Certificate.accept leaf of the A25 SwitchBatch (Lean-green)
must pass the transcribed switchDirectUpperQ <= bound, and the accepted leaves must tile [0,1571/1000].
Negative control: shrinking the bound by 1e-3 must reject some leaf."""
import re,sys,time,json
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent)); import switch_kernel as K
src=Path('/workspace/work/dcp-n11-lean/wip/lean/N11Formalization/SharedMomentConcreteSwitchBatch.lean').read_text()
vals={}
for m in re.finditer(r'def start0_switch(\d)_(p|q|b|d2|d1|bound) : ℚ := \((.*?) : ℚ\)',src): vals.setdefault(int(m.group(1)),{})[m.group(2)]=F(m.group(3).strip('()'))
pat=re.compile(r'theorem start0_switch(\d)_node_\d+ : Certificate start0_switch\d_leaf\n    \(switchCell \((.*?) : ℚ\) \((.*?) : ℚ\)\) := by\n  apply Certificate.accept')
leaves={}
for m in pat.finditer(src): leaves.setdefault(int(m.group(1)),[]).append((F(m.group(2)),F(m.group(3))))
out={}
for k in range(9):
  c=vals[k]; L=sorted(leaves[k]); t=time.time()
  ok=all(K.switchDirectUpperQ(c['p'],c['q'],c['b'],c['d2'],c['d1'],lo,hi)<=c['bound'] for lo,hi in L)
  tile=L[0][0]==0 and L[-1][1]==K.ROOT_HI and all(L[i][1]==L[i+1][0] for i in range(len(L)-1))
  neg=not all(K.switchDirectUpperQ(c['p'],c['q'],c['b'],c['d2'],c['d1'],lo,hi)<=c['bound']-F(1,1000) for lo,hi in L)
  out[k]=dict(leaves=len(L),all_accept=ok,tiles=tile,neg_control_rejects=neg,sec=round(time.time()-t,2))
  print(k,out[k],flush=True)
json.dump(out,open(Path(__file__).parent.parent/'data'/'control_batch.json','w'),indent=1)
