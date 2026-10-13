"""Replay saved rational leaf cover without numerical LP. Verifies exact
recursive domain partition; replays illegal leaves and selected/all atomic
leaves. Canonical unit-vector file removes platform tan from replay inputs.
"""
import hubline_domain as D
import json,sys,hashlib,time
from fractions import Fraction as F
from pathlib import Path
P=D.H.K.P
canonical=json.loads((P/'evidence/atomic-unit-vectors-2048.json').read_text())
V=[(F(c),F(s)) for c,s in canonical]
assert len(V)==2048 and all(c*c+s*s==1 for c,s in V)
old=D.AF.A.units
def units(n):return V if n==2048 else old(n)
D.AF.A.units=units
INPUT=Path(sys.argv[2]) if len(sys.argv)>2 else D.OUT
INPUT_BYTES=INPUT.read_bytes()
state=json.loads(INPUT_BYTES);leaves=state['leaves'];pending=state['pending']
ends={}
for leaf in leaves:
 key=D.decode(leaf['H']);assert key not in ends;ends[key]=leaf['type']
for B in pending:
 key=D.decode(B);assert key not in ends;ends[key]='pending'
root=D.decode(state['domain']);seen=set()
def check(B):
 if B in ends:seen.add(B);return
 widths=[h-l for l,h in B];j=max(range(3),key=lambda k:widths[k]);l,h=B[j];m=(l+h)/2
 assert h-l>F(1,10**8),'partition gap or unexpected split'
 for pair in [(l,m),(m,h)]:child=list(B);child[j]=pair;check(tuple(child))
check(root);assert seen==set(ends)
# All invalid hub boxes use a valid necessary-condition test anew.
for leaf in leaves:
 if leaf['type']=='infeasible':assert D.infeasible(D.decode(leaf['H']))
atoms=[v for v in leaves if v['type']=='atomic'];mode=sys.argv[1] if len(sys.argv)>1 else 'sample'
if mode=='all':indices=list(range(len(atoms)))
else:indices=sorted(set([0,len(atoms)//4,len(atoms)//2,3*len(atoms)//4,len(atoms)-1])) if atoms else []
t=time.time();results=[]
for i in indices:
 v=atoms[i];C=D.AF.FastAtoms(D.decode(v['H']),v['proposal']['weights'],2048);r=C.certify(200000)
 assert r['status']=='certified',(i,r)
 for key in ['boxes','leaves','outside','max_integer_capture','total_integer_demand','gap_integer','atoms']:assert r[key]==v['result'][key],(i,key,r[key],v['result'][key])
 results.append({'index':i,'result':r})
 if len(results)%100==0:print('replayed',len(results),'seconds',time.time()-t,flush=True)
out={'status':'full replay' if mode=='all' and not pending else 'partial replay','partition':'exact recursive full root cover','leaves':len(leaves),'pending':len(pending),'atomic_leaves':len(atoms),'replayed':len(results),'results':results,'seconds':time.time()-t,'input_sha256':hashlib.sha256(INPUT_BYTES).hexdigest(),'canonical_vectors_sha256':hashlib.sha256((P/'evidence/atomic-unit-vectors-2048.json').read_bytes()).hexdigest()}
(P/'evidence'/('hubline-domain-replay-'+mode+'.json')).write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='results'}),flush=True)
