"""Exact formal coefficient audit of shared-factor dual; no trig evaluation/helpers.
Independent dictionary of linear terms in formal area/side/radius/angle/width atoms.
"""
from pathlib import Path
from fractions import Fraction as Q
import json
P=Path(__file__).parent;reports=[]
for start in [0,2]:
 j=json.loads((P/f'shared_moment_dense_{start}_4.json').read_text());faces=j['faces'];edges=[tuple(e) for e in j['edges']];z=[Q(f'{v:.9f}') for v in j['z']]
 L={};E={}
 def put(d,key,v):d[key]=d.get(key,Q(0))+v
 # L: expand the assembled factor sum minus exact area, no maximization
 put(L,'pi',sum(z[:9])+2*sum(z[9:11])+sum(z[50:71])-2*z[71]-2*z[72]);put(L,'asin2R',2*z[72])
 for t,f in enumerate(faces):
  for k,i in enumerate(f):
   e=tuple(sorted(v for v in f if v!=i));ei=edges.index(e);adj=[tt for tt,ff in enumerate(faces) if all(v in ff for v in e)];sgn=1 if adj[0]==t else -1
   put(L,('angle',t,i),-z[i]-z[50+ei]);put(L,('side2',t,ei),sgn*z[11+ei]);put(L,('side1',t,ei),sgn*z[73+ei])
 for bi in range(9):
  i,jj=bi,(bi+1)%9;ei=edges.index(tuple(sorted((i,jj))))
  put(L,('b',bi),z[i]+z[jj]-z[50+ei]);put(L,('switch-side2',bi),-z[11+ei]);put(L,('switch-radius2',bi),z[32+2*i+1]+z[32+2*jj]);put(L,('switch-side1',bi),-z[73+ei]);put(L,('switch-radius1',bi),z[94+2*i+1]+z[94+2*jj])
 for i in range(9):
  put(L,('alpha',i),-z[i]);put(L,('width',i),z[71]+(z[72] if i>=3 else 0));put(L,('copy-left2',i),-z[32+2*i]);put(L,('copy-right2',i),-z[32+2*i+1]);put(L,('copy-left1',i),-z[94+2*i]);put(L,('copy-right1',i),-z[94+2*i+1])
 # E: independent assembly as multiplier * exact residual; widths/edge slacks nonnegative
 for i in range(11):
  put(E,'pi',z[i]*(1 if i<9 else 2))
  for t,f in enumerate(faces):
   if i in f:put(E,('angle',t,i),-z[i])
  if i<9:
   put(E,('alpha',i),-z[i]);put(E,('b',(i-1)%9),z[i]);put(E,('b',i),z[i])
 for ei,(i,jj) in enumerate(edges):
  adj=[(t,next(v for v in f if v not in (i,jj))) for t,f in enumerate(faces) if i in f and jj in f]
  put(E,'pi',z[50+ei])
  for k,(t,v) in enumerate(adj):put(E,('side2',t,ei),(1 if k==0 else -1)*z[11+ei]);put(E,('side1',t,ei),(1 if k==0 else -1)*z[73+ei]);put(E,('angle',t,v),-z[50+ei])
  if len(adj)==1:
   bi=next(b for b in range(9) if {b,(b+1)%9}=={i,jj});put(E,('switch-side2',bi),-z[11+ei]);put(E,('switch-side1',bi),-z[73+ei]);put(E,('b',bi),-z[50+ei])
 for i in range(9):
  for isright in [0,1]:
   coef=z[32+2*i+isright];put(E,('switch-radius2',i if isright else (i-1)%9),coef);put(E,('copy-right2' if isright else 'copy-left2',i),-coef);coef1=z[94+2*i+isright];put(E,('switch-radius1',i if isright else (i-1)%9),coef1);put(E,('copy-right1' if isright else 'copy-left1',i),-coef1)
  put(E,('width',i),z[71]+(z[72] if i>=3 else 0))
 put(E,'pi',-2*z[71]-2*z[72]);put(E,'asin2R',2*z[72])
 assert all(L.get(k,0)==E.get(k,0) for k in set(L)|set(E))
 reports.append({'start':start,'span':4,'formal_atoms':len(L),'exact_identity':True})
core=[0,2,3,4,5,6,7,8];orbits={}
for s in range(8):
 c=core[s:]+core[:s];a=set(c[:5]);b=set(c[4:]+c[:1])
 def key(a,b):return tuple(sorted((tuple(sorted(a)),tuple(sorted(b)))))
 k=min(key(a,b),key({(2-i)%9 for i in a},{(2-i)%9 for i in b}));orbits.setdefault(k,[]).append(s)
assert sorted(orbits.values())==[[0,1,4,5],[2,3,6,7]]
(P/'shared_moment_dense_symbolic_control.json').write_text(json.dumps({'formal_checks':reports,'orbits':list(orbits.values())},indent=2));print('Exact rational coefficient cancellation, two balanced graphs; reflection orbits verified.')
