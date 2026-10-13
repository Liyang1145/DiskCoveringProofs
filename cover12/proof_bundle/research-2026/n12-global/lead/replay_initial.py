"""Bounded read-only replay of C182 with exact controls. Run from workspace root."""
from pathlib import Path
from fractions import Fraction as F
import sys, json, subprocess, hashlib, time, os
ROOT=Path.cwd(); OLD=ROOT/'research-2026/session2/n1314/py'
sys.path.insert(0,str(OLD))
import certlib as L, cert_bb as B, cert_cand as C
OUT=ROOT/'research-2026/n12-global/evidence/initial-replay'; OUT.mkdir(parents=True,exist_ok=True)
controls={}
for q in [F(0),F(1),F(2),F(9,16),F(1,10**60),F(10**20,3)]:
    lo,hi=L._sqrt_pair(q); assert lo>=0 and lo*lo<=q<hi*hi
controls['sqrt_exact_squared_inequalities']=True
box=((F(-1),F(1)),(F(-1),F(1)))
assert L.dist_box_hi(box,(F(0),F(0)))**2>=2
ok,st=B.bb_upper([(F(0),F(0))],F(3,2),maxdepth=10,maxboxes=10000)
assert ok; controls['positive_center_origin_r1.5']=st
ok,st=B.bb_upper([(F(0),F(0))],F(9,10),maxdepth=8,maxboxes=10000)
assert not ok and B.point_lower([(F(0),F(0))],(F(1),F(0)))>F(9,10)
controls['negative_center_origin_r0.9']={'returned':ok,'reason':st,'independent_point':'(1,0), exact distance=1'}
d=C.enclose([(F(1,4),F(0))]); assert d['lo']<=F(5,4)<=d['hi']
controls['D2_one_nonzero_center_radius1.25']={k:str(v) for k,v in d.items()}
cfg=ROOT/'research-2026/session2/n1314/cfg/cert_n12_othern.json'
raw=json.loads(cfg.read_text())['centers_dec17']; parsed=C.load_frac_centers(cfg,'centers_dec17',17)
assert parsed==[tuple(F(x) for x in p) for p in raw]
controls['all24_literal_identity']=True
files=[cfg,OLD/'certify_cfg.py',OLD/'cert_bb.py',OLD/'cert_cand.py',OLD/'certlib.py']
controls['sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(OUT/'controls.json').write_text(json.dumps(controls,indent=2),encoding='utf-8')
cmd=[sys.executable,'-B',str(OLD/'certify_cfg.py'),str(cfg),'--key','centers_dec17','--nd','17','--claim','0.361102963744508672616920293904']
t=time.time()
with (OUT/'c182-d1-d2-replay.txt').open('w',encoding='utf-8') as log:
    try:
        p=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=180,env={**os.environ,'PYTHONIOENCODING':'utf-8'})
        result={'command':cmd,'exit':p.returncode,'seconds':time.time()-t}
    except subprocess.TimeoutExpired:
        result={'command':cmd,'timeout':180,'classification':'budget stop, not mathematical disproof'}
(OUT/'run.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps(result))
