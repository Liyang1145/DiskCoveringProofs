"""Bounded coupled-dual reoptimization. Sampled LP only proposes rational certificate inputs."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from joint_innernorm_probe import *
from all_face_pack_certificate import certify_pack,sc,costerm
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
   loss=r*r/2*min(1-math.cos(t)for t in ts)*abs(sum(ts)-math.pi)
   for e,t in zip(ee,ts):
    for v in e:mat[at,v]-=t
   mat[at,16+q+k]=-1;rhs[at]=-r*r*sum(math.sin(t)for t in ts)+loss;at+=1
 for k,(u,v)in enumerate(single):
  for t in grid:
   mat[at,u]=-t;mat[at,v]=-t;mat[at,16+q+len(groups)+k]=-1;rhs[at]=-r*r*math.sin(t);at+=1
 lp=linprog(np.r_[np.full(14,2*math.pi),-2*math.pi,-2*math.pi,np.ones(N-16)],A_ub=mat.tocsr(),b_ub=rhs,bounds=[(None,None)]*14+[(0,None)]*2+[(None,None)]*(N-16),method='highs');assert lp.success
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
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());tests=json.loads((P/'all-face-pack-catalogue.json').read_text())['runs'];ret={(x['family'],x['index'])for x in json.loads((P/'all-face-pack-retained.json').read_text())['retained']};out=[];start=time.time()
 with (P/'pack-reopt-catalogue.jsonl').open('w') as stream:
  for test in tests:
   fam=test['family'];idx=test['index']
   if (fam,idx)not in ret:continue
   q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});pack=test.get('faces') or [p['face']for p in test.get('parts',[])];assert pack
   row=optimize(q,edges,faces,pack);row.update(family=fam,index=idx)
   if row['sampled_lp_not_bound']<0:cert=certify_pack(q,edges,faces,row,pack,6000)
   else:cert={'family':fam,'index':idx,'status':'inconclusive','reason':'sampled LP no negative proposal'}
   rec={'row':row,'certificate':cert};out.append(rec);stream.write(json.dumps(rec)+'\n');stream.flush();sc.cache_clear();costerm.cache_clear()
   if len(out)%20==0:print(len(out),'excluded',sum(x['certificate']['status']=='excluded'for x in out),'seconds',time.time()-start,flush=True)
 (P/'pack-reopt-catalogue.json').write_text(json.dumps({'status':'interval_certificates_new_dual_proposals','runs':out},indent=2));print('DONE',len(out),sum(x['certificate']['status']=='excluded'for x in out),time.time()-start,flush=True)
