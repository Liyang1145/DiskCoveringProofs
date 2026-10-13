"""Bounded numeric anchor-value diagnostic; no rank or continuum certificate."""
import json,numpy as np
from fixed_anchor_convex_probe import P,solve_case
src=json.loads((P/'fixed-anchor-convex-probe.json').read_text())['runs'][0]
C=np.array(src['centers']); A=np.array(src['anchors']); W=np.array(src['witnesses'])
keep=[0,2,3,5,6,8,9,11]; faces=[src['faces'][i]for i in keep]; owners=src['owners']
assert len(faces)*3+sum(map(len,owners))==44
th=np.unwrap(np.arctan2(A[:,1],A[:,0]));rstar=.3317320342762341225578
vecs={'fixedstress_obstruction':np.array([0,-1/4,-2/3,-13/12,-4/3,-4/3,-13/12,-2/3,-1/4,0.])}
v=np.zeros(10);v[[0,9]]=1;vecs['rotate_Xplus_pair']=v
v=np.zeros(10);v[1]=1;vecs['one_noncap_anchor']=v
v=np.zeros(10);v[0]=-1;v[9]=1;vecs['shrink_Xplus_cap']=v
rows=[]
for name,v in [('control',np.zeros(10))]+list(vecs.items()):
 for step in ([0.]if name=='control'else[1e-4,1e-3]):
  tt=th+step*v;aa=np.c_[np.cos(tt),np.sin(tt)];gaps=np.diff(np.r_[tt,tt[0]+2*np.pi]);assert min(gaps)>0 and max(gaps)<=2*np.arcsin(rstar)+1e-14
  row=solve_case(name,C,aa,faces,owners,W[keep]); row.update(step=step,delta_radius=row['radius']-rstar,max_gap=float(max(gaps)),scope='numeric only; approximate saved candidate anchors; solver not certificate')
  rows.append(row)
(P/'q10-relaxed-anchor-probe.json').write_text(json.dumps(dict(status='numeric_only',source='fixed-anchor-convex-probe.json runs[0], approximate primal/anchors',rows=rows),indent=2))
print('SUMMARY',[(x['case'],x['step'],x['delta_radius'],x['min_constraint'],x['dual_force_residual'])for x in rows])
