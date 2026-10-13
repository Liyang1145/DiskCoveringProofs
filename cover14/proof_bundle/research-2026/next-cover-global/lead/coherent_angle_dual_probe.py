"""Numeric bounded factor-dual plus coherent Delaunay-angle linear constraints."""
from all_face_consistency_probe import envelope
from joint_innernorm_probe import *
from itertools import product
import time

def solve(q,edges,faces,nfg=11):
 nf=len(faces);ne=len(edges);ee=[[tuple(sorted(e))for e in combinations(f,2)]for f in faces];inc=[[(f,ee[f].index(e))for f in range(nf)if e in ee[f]]for e in edges];bedges=[k for k in range(ne)if len(inc[k])==1];nb=len(bedges)
 iw=16;ip=iw+nf;ia=ip+3*nf;ibeta=ia+nf;it=ibeta+ne;ih=it+14;ihA=ih+3*nf;ib=ihA+nb;ie=ib+q;iff=ie+ne;N=iff+nf
 grid=np.linspace(0,math.pi,61);fg=np.linspace(0,math.pi,nfg);samples=[(ts,envelope(ts))for ts in product(fg,repeat=3)if sum(ts)<=2*math.pi+1e-12];M=2*q*len(grid)+nf*len(samples)+ne*(len(grid)+1)+3*nf+nb;mat=lil_matrix((M,N));rhs=np.zeros(M);at=0
 for j in range(q):
  for t in grid:
   h=min(float(a)+float(k)*t for a,k in lines)
   mat[at,j]=-t;mat[at,it+j]=-t;mat[at,14]=bv(t);mat[at,15]=h;mat[at,ib+j]=-1;rhs[at]=-fval(t,0);at+=1
   mat[at,j]=-t;mat[at,it+j]=-t;mat[at,14]=An;mat[at,15]=h;mat[at,ib+j]=-1;rhs[at]=-cAn;at+=1
 for f in range(nf):
  for ts,A in samples:
   mat[at,iw+f]=A
   for k,t in enumerate(ts):mat[at,ip+3*f+k]=-t
   mat[at,iff+f]=-1;at+=1
 for k,(u,v)in enumerate(edges):
  for t in grid:
   a=r*r*math.sin(t);mat[at,u]=-t;mat[at,v]=-t;mat[at,ibeta+k]=-t
   for f,j in inc[k]:mat[at,iw+f]=-a;mat[at,ip+3*f+j]=t
   mat[at,ie+k]=-1;rhs[at]=-a;at+=1
  for f,j in inc[k]:mat[at,iw+f]=1
  rhs[at]=1;at+=1
 for f in range(nf):
  for j,e in enumerate(ee[f]):
   opp=next(v for v in faces[f]if v not in e);mat[at,ia+f]=-1;mat[at,ibeta+edges.index(e)]=-1;mat[at,it+opp]=-1;mat[at,ih+3*f+j]=-1;at+=1
 for j,k in enumerate(bedges):
  u,v=edges[k];mat[at,ibeta+k]=-1;mat[at,it+u]=1;mat[at,it+v]=1;mat[at,ihA+j]=-1;at+=1
 assert at==M
 obj=np.zeros(N);obj[:14]=2*math.pi;obj[14:16]=-2*math.pi;obj[ia:ibeta]=math.pi;obj[ibeta:it]=math.pi;obj[it:ih]=[math.pi if v<q else 2*math.pi for v in range(14)];obj[ih:ihA]=math.pi;obj[ihA:ib]=math.pi/2;obj[ib:]=1
 bounds=[(None,None)]*N
 for j in[14,15]:bounds[j]=(0,None)
 for j in range(iw,ip):bounds[j]=(0,1)
 for j in range(ih,ib):bounds[j]=(0,None)
 lp=linprog(obj,A_ub=mat.tocsr(),b_ub=rhs,bounds=bounds,method='highs');assert lp.success,lp.message
 return {'sampled_lp_not_bound':float(lp.fun-math.pi),'potentials':lp.x[:14].tolist(),'nu':float(lp.x[14]),'lambda':float(lp.x[15]),'weights':lp.x[iw:ip].tolist(),'face_potentials':lp.x[ip:ia].reshape(nf,3).tolist(),'face_angle_multipliers':lp.x[ia:ibeta].tolist(),'edge_angle_multipliers':lp.x[ibeta:it].tolist(),'vertex_angle_multipliers':lp.x[it:ih].tolist(),'grid_size':nfg}
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());data=json.loads((P/'all-face-consistency-probe.json').read_text())['runs'];G=json.loads((P/'stress-barycentric-result.json').read_text());out=[];start=time.time()
 for old in data:
  fam=old['family'];idx=old['index'];q=10 if fam=='candidate'else int(fam.split('/')[0]);faces=([x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]])if fam=='candidate'else(D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'])
  if fam=='candidate':
   bd=sorted({v for e in {tuple(sorted(e))for f in faces for e in combinations(f,2)}if sum(all(v in f for v in e)for f in faces)==1 for v in e});perm=bd+[v for v in range(14)if v not in bd];faces=[[perm.index(v)for v in f]for f in faces]
  edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});row=solve(q,edges,faces);row.update(family=fam,index=idx,old_sampled_lp=old['sampled_lp_not_bound']);out.append(row);print(fam,idx,'coherent',row['sampled_lp_not_bound'],'old',old['sampled_lp_not_bound'],'seconds',time.time()-start,flush=True)
 (P/'coherent-angle-dual-probe.json').write_text(json.dumps({'status':'numeric_only_coherent_angle_factor_dual','runs':out},indent=2))
