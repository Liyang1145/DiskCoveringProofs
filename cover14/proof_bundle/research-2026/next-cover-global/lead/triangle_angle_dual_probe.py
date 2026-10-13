"""Numeric dual proposal in real triangle angles, not independent beta factors."""
from joint_innernorm_probe import *
import time

def solve(q,faces,n=31):
 edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});bedges=[e for e in edges if sum(all(v in f for v in e)for f in faces)==1];nf=len(faces);nb=len(bedges);ib=16;it=ib+q;ig=it+nf;N=ig+nb;grid=np.linspace(0,math.pi,81);ggrid=np.linspace(0,math.pi/2,81);tri=[(math.pi*i/n,math.pi*j/n,math.pi*(n-i-j)/n)for i in range(n+1)for j in range(n+1-i)];M=2*q*len(grid)+nf*len(tri)+nb*len(ggrid);mat=lil_matrix((M,N));rhs=np.zeros(M);at=0
 for v in range(q):
  for t in grid:
   h=min(float(a)+float(k)*t for a,k in lines)
   mat[at,v]=-t;mat[at,14]=bv(t);mat[at,15]=h;mat[at,ib+v]=-1;rhs[at]=-fval(t,0);at+=1
   mat[at,v]=-t;mat[at,14]=An;mat[at,15]=h;mat[at,ib+v]=-1;rhs[at]=-cAn;at+=1
 for j,f in enumerate(faces):
  for ts in tri:
   for v,t in zip(f,ts):mat[at,v]=-t
   mat[at,it+j]=-1;rhs[at]=-2*r*r*math.prod(math.sin(t)for t in ts);at+=1
 for j,(u,v)in enumerate(bedges):
  for g in ggrid:mat[at,u]=g;mat[at,v]=g;mat[at,ig+j]=-1;rhs[at]=-r*r/2*math.sin(2*g);at+=1
 obj=np.r_[[math.pi if v<q else 2*math.pi for v in range(14)],-2*math.pi,-2*math.pi,np.ones(N-16)];lp=linprog(obj,A_ub=mat.tocsr(),b_ub=rhs,bounds=[(None,None)]*14+[(0,None)]*2+[(None,None)]*(N-16),method='highs');assert lp.success
 return {'sampled_lp_not_bound':float(lp.fun-math.pi),'potentials':lp.x[:14].tolist(),'nu':float(lp.x[14]),'lambda':float(lp.x[15]),'triangle_supports':lp.x[it:ig].tolist(),'grid_n':n}
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());data=json.loads((P/'all-face-consistency-probe.json').read_text())['runs'];G=json.loads((P/'stress-barycentric-result.json').read_text());out=[];start=time.time()
 for old in data:
  fam=old['family'];idx=old['index'];q=10 if fam=='candidate'else int(fam.split('/')[0]);faces=([x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]])if fam=='candidate'else(D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'])
  if fam=='candidate':
   bd=sorted({v for e in {tuple(sorted(e))for f in faces for e in combinations(f,2)}if sum(all(v in f for v in e)for f in faces)==1 for v in e});perm=bd+[v for v in range(14)if v not in bd];faces=[[perm.index(v)for v in f]for f in faces]
  row=solve(q,faces);row.update(family=fam,index=idx,old_sampled_lp=old['sampled_lp_not_bound']);out.append(row);print(fam,idx,'triangle',row['sampled_lp_not_bound'],'paired',old['sampled_lp_not_bound'],'seconds',time.time()-start,flush=True)
 (P/'triangle-angle-dual-probe.json').write_text(json.dumps({'status':'numeric_only_real_triangle_angle_dual','runs':out},indent=2))
