"""Independent scalar rational q10 normalizedpolytope clipping. No memberclipping imports."""
from fractions import Fraction as Q
from q11_split_basis_audit import inv
from q11_split_inductive_audit import rowbasis
from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent

def scalar(t):
 a,b,c=map(Q,t);assert b==0 and a==-10*c;return -c

def decode(p):
 assert list(map(Q,p['equality'][0]))==[Q(1)]*10 and scalar(p['equality'][1])==1
 return {tuple(scalar(t)for t in v)for v in p['vertex_set']},[(tuple(map(Q,n)),scalar(r))for n,r,_ in p['inequalities']]

def clip(V,cs,n,r):
 dot=lambda a,b:sum(x*y for x,y in zip(a,b));V=sorted(V);active=[]
 for v in V:
  assert sum(v)==1;slacks=[dot(nn,v)-rr for nn,rr in cs];assert min(slacks)>=0;aa={i for i,s in enumerate(slacks)if s==0};assert len(rowbasis([[Q(1)]*10]+[list(cs[i][0])for i in aa]))==10;active.append(aa)
 vv=[dot(n,v)-r for v in V];cross=set();cache={}
 for i,u in enumerate(V):
  for j in range(i):
   if vv[i]*vv[j]>=0:continue
   common=tuple(sorted(active[i]&active[j]))
   if len(common)<8:continue
   if common not in cache:cache[common]=len(rowbasis([[Q(1)]*10]+[list(cs[k][0])for k in common]))
   if cache[common]!=9:continue
   # Scalar rational edge interpolation, genuinely different from Q³ active-systemsolve.
   t=vv[i]/(vv[i]-vv[j]);w=tuple((1-t)*x+t*y for x,y in zip(u,V[j]));assert dot(n,w)==r and all(dot(nn,w)>=rr for nn,rr in cs);cross.add(w)
 return ({v for v,s in zip(V,vv)if s>=0}|cross,{v for v,s in zip(V,vv)if s<=0}|cross)

if __name__=='__main__':
 src=P/'q10-metric-slab-controls.json';raw=src.read_bytes();a=json.loads(raw);base=json.loads((P/'q10-reduced-metric-domain.json').read_text())['polytope'];V,cs=decode(base);audit=json.loads((P/'q10-reduced-domain-audit.json').read_text());assert audit['source_sha256']==hashlib.sha256((P/'q10-reduced-metric-domain.json').read_bytes()).hexdigest();assert V=={tuple(map(Q,v))for v in audit['normalized_vertices']};out=[]
 from q11_chord_flow_fraction_replay import replay
 for row in a['runs']:
  cp=row['polytope'];VV,cc=decode(cp);assert cc[:-1]==cs;n,r=cc[-1];assert n==tuple(Q(row['side'])*int(i<row['prefix'])for i in range(10))and r==Q(row['side'])*Q(row['threshold_total_fraction']);expected,_=clip(V,cs,n,r);assert VV==expected;cert=row['certificate'];assert {tuple(scalar(t)for t in v)for v in cert['polytope']['vertices']}==VV;assert cert['index']==879 and cert['flow']['faces']==json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][879]['faces'];rr=replay(cert);out.append({'prefix':row['prefix'],'side':row['side'],'threshold':row['threshold_total_fraction'],'vertices':len(VV),'replay':rr});print('RATIONALCLIP',row['prefix'],row['side'],len(VV),rr['excluded'],flush=True)
 (P/'q10-metric-slab-audit.json').write_text(json.dumps({'status':'independent_rational_clipping_and_fractionbounds','source_sha256':hashlib.sha256(raw).hexdigest(),'runs':out},indent=2))
