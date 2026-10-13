"""Calibration between independently assembled numerical atoms and interval objective.
Not a proof by sampling; formal coefficient proof is separate.
"""
from pathlib import Path
import json,sys,random
P=Path(__file__).parent
s=(P/'exchange_middle_inward_dual.py').read_text();marker='\n# Finite LP planes';assert s.count(marker)==1
ns={'__file__':str(P/'exchange_middle_inward_dual.py')};exec(s.split(marker)[0],ns)
z=ns['np'].array([float(f'{x:.9f}') for x in json.loads((P/'middle_inward_frozen.json').read_text())['z']])
sys.argv=['x','0','4'];s=(P/'certify_q0_closure.py').read_text();assert s.count('# Heap entries')==1;s=s.split('# Heap entries')[0].replace("f'q0_closure_dual_{start}_{span}.json'","'middle_inward_frozen.json'")
kn={'__file__':str(P/'certify_q0_closure.py')};exec(s,kn);iv=kn['iv'];rng=random.Random(911);count=0
for fi in range(29):
 for _ in range(20):
  if fi<11:
   a=rng.uniform(.01,3.);b=rng.uniform(.001,3.141592653589793-a);t=ns['radiusarg'](fi,[a,b],z);x=[a,b,t];box=x[:2]
  elif fi<20:
   b=rng.uniform(.001,1.56);t=ns['radiusarg'](fi,[b],z);x=[b,t];box=x[:1]
  else:
   x=[rng.uniform(.03,3.14),rng.uniform(.1,1),rng.uniform(.1,1)];box=x
  val=ns['value'](fi,x,z);encl=kn['factors'][fi][1]([iv.mpf([v-1e-10,v+1e-10])for v in box])
  if encl is None:continue
  assert float(encl.a)-1e-12<=val<=float(encl.b)+1e-12,(fi,val,str(encl));count+=1
out={'calibration_points':count,'all_contained_with_1e-12_double_guard':True,'scope':'different atom assembly vs intervalobjective; NOT continuumproof; randominputboxes only'}
(P/'middle_atom_interface_control.json').write_text(json.dumps(out,indent=2));print(out)
