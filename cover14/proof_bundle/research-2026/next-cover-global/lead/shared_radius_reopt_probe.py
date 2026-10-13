"""Bounded coupled-dual reoptimization. Sampled LP only proposes rational certificate inputs."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from joint_innernorm_probe import *
from shared_radius_pack_certificate import certify_pack,sc,costerm
import time

def optimize(q,edges,faces,pack):
 used=set();groups=[]
 for f in pack:
  ee=[tuple(sorted(e))for e in combinations(faces[f],2)];assert not used.intersection(ee);used.update(ee);groups.append(ee)
 single=[e for e in edges if e not in used];N=16+q+len(groups)+len(single);grid=np.linspace(0,math.pi,61);fg=np.linspace(0,math.pi,11);mrows=2*q*len(grid)+len(groups)*len(fg)**3+len(single)*len(grid);mat=lil_matrix((mrows,N));rhs=np.zeros(mrows);at=0
 for j in range(q):
  for t in grid:
   h=min(float(a)+float(k)*t for a,k in lines)
   mat[at,j]=-t;mat[at,14]=bv(t);mat[at,15]=h;mat[at,16+j]=-1;rhs[at]=-fval(t,0);at+=1
   mat[at,j]=-t;mat[at,14]=An;mat[at,15]=h;mat[at,16+j]=-1;rhs[at]=-cAn;at+=1
 from itertools import product
 for k,ee in enumerate(groups):
  for ts in product(fg,repeat=3):
   if sum(ts)>2*math.pi+1e-12:continue
   loss=r*r/2*min(1-math.cos(t)for t in ts)*abs(sum(ts)-math.pi)
   if math.pi+1e-10<sum(ts)<2*math.pi-1e-10:
    a=sum(math.sin(t)for t in ts);b=sum(math.sin(u+v)for u,v in combinations(ts,2));c=math.sin(sum(ts))
    if a>1e-10:
     x0=max(0,min(1,(b+math.sqrt(max(0,b*b-4*a*c)))/(2*a)));loss=max(loss,r*r*(1-x0)*a)
   for e,t in zip(ee,ts):
    for v in e:mat[at,v]-=t
   mat[at,16+q+k]=-1;rhs[at]=-r*r*sum(math.sin(t)for t in ts)+loss;at+=1
 for k,(u,v)in enumerate(single):
  for t in grid:
   mat[at,u]=-t;mat[at,v]=-t;mat[at,16+q+len(groups)+k]=-1;rhs[at]=-r*r*math.sin(t);at+=1
 lp=linprog(np.r_[np.full(14,2*math.pi),-2*math.pi,-2*math.pi,np.ones(N-16)],A_ub=mat.tocsr()[:at],b_ub=rhs[:at],bounds=[(None,None)]*14+[(0,None)]*2+[(None,None)]*(N-16),method='highs');assert lp.success
 y=[Q(format(v,'.12f'))for v in lp.x[:14]];nu=max(Q(0),Q(format(lp.x[14],'.12f')));lam=max(Q(0),Q(format(lp.x[15],'.12f')));ts=[]
 for j in range(q):
  pts=[0,float((verts[1][0].lo+verts[1][0].hi)/(2*S)),float((verts[2][0].lo+verts[2][0].hi)/(2*S)),math.pi];cand=list(pts)
  for seg in range(3):
   slope=float(lines[seg][1]);g=lambda t:fn(t,float(nu))+float(lam)*slope-float(y[j]);lo,hi=pts[seg],pts[seg+1]
   if g(lo)>0 and g(hi)<0:cand.append(brentq(g,lo,hi))
  t=max(cand,key=lambda t:fval(t,float(nu))+float(lam)*min(float(a)+float(k)*t for a,k in lines)-float(y[j])*t);ts.append(max(Q(0),min(Q('3.141592653589'),Q(format(t,'.12f')))))
 for u,v in edges:
  pot=float(y[u]+y[v]);t=0 if pot>=r*r else(math.pi if pot<=-r*r else math.acos(pot/(r*r)));ts.append(max(Q(0),min(Q('3.141592653589'),Q(format(t,'.12f')))))
 return {'rational_angles':list(map(str,ts)),'rational_potentials':list(map(str,y)),'rational_nu':str(nu),'rational_lambda':str(lam),'sampled_lp_not_bound':float(lp.fun-math.pi)}

if __name__=='__main__':
 G=json.loads((P/'stress-barycentric-result.json').read_text());faces=[x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});row=optimize(10,edges,faces,[14,15]);row.update(family='candidate',index=-1);cert=certify_pack(10,edges,faces,row,[14,15],12000);assert cert['status']!='excluded';out=[{'row':row,'certificate':cert}];print('candidate',row['sampled_lp_not_bound'],cert['upper_display'],flush=True)
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());ret={(x['family'],x['index'])for x in json.loads((P/'pack-reopt-retained.json').read_text())['retained']};tests=json.loads((P/'pack-reopt-catalogue.json').read_text())['runs'];selected=[]
 for fam in ['10/4','11/3']:
  rr=sorted([x for x in tests if x['row']['family']==fam and (fam,x['row']['index'])in ret],key=lambda x:x['row']['sampled_lp_not_bound'])[:6];selected+=rr
 for test in selected:
  fam=test['row']['family'];idx=test['row']['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});pack=[p['face']for p in test['certificate']['parts']];row=optimize(q,edges,faces,pack);row.update(family=fam,index=idx);cert=certify_pack(q,edges,faces,row,pack,6000);out.append({'row':row,'certificate':cert});print(fam,idx,row['sampled_lp_not_bound'],cert['status'],cert['upper_display'],flush=True);sc.cache_clear();costerm.cache_clear()
 (P/'shared-radius-reopt-probe.json').write_text(json.dumps({'status':'numeric_LP_proposals_interval_certificates_pending_replay','runs':out},indent=2))
