"""Re-emit Rep1S2..S8 and Q0M2S0..S8 core switch replays with smaller parts (OOM fix). Leaves Control0/Rep1S0/S1 untouched."""
import os,json,sys
os.environ.setdefault('PART','100'); os.environ.setdefault('CHUNK','25')
sys.path.insert(0,os.path.dirname(__file__))
import gen_core_switch as g
from fractions import Fraction as F
allm=['Class33Core/Defs','Class33Core/SwitchKernel','Class33Core/Rep1','Class33Core/Q0M2']
for tab,mod,js in [('rep1','Rep1',range(2,9)),('q0m2','Q0M2',range(9))]:
  d=json.loads((g.ROOT/'data'/f'switch_trees_{tab}.json').read_text())
  for j in js:
    name=f'{mod}S{j}'
    for f in g.OUT.glob(f'{name}P*.lean'): f.unlink()
    r=d[str(j)]
    allm+=['Class33Core/SwTrees/'+m for m in g.emit(name,f'import Class33Core.{mod}',f'⟨{mod}.table.switchP {j},{mod}.table.switchQ {j},{mod}.table.switchB {j},{mod}.table.switchD2 {j},{mod}.table.switchD1 {j}⟩',F(r['M']),r['leaves'],f'{tab} Lean switch {j}, M={r["M"]} (hist upper {r["hist_upper"]:.8f})')]
t=g.ROOT/'data'/'core_modules_v2.txt.tmp'; t.write_text('\n'.join(allm)+'\n'); os.replace(t,g.ROOT/'data'/'core_modules_v2.txt'); print(len(allm))
