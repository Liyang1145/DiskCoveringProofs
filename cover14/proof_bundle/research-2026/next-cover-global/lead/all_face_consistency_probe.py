"""Sampled LP only: all-face exact envelopes with independentlyallocatededgepotentials."""
from joint_innernorm_probe import *
from itertools import product
import time

def envelope(ts):
 B=sum(ts);a=sum(math.sin(t)for t in ts);loss=.5*min(1-math.cos(t)for t in ts)*abs(B-math.pi)
 if math.pi+1e-10<B<2*math.pi-1e-10 and a>1e-10:
  b=sum(math.sin(u+v)for u,v in combinations(ts,2));c=math.sin(B);x=max(0,min(1,(b+math.sqrt(max(0,b*b-4*a*c)))/(2*a)));loss=max(loss,(1-x)*a)
 if B<math.pi and B+min(ts)>=math.pi-1e-13:
  d=(math.pi-B)/2;loss=max(loss,min(2*math.sin(t)*math.sin(t/2)*math.sin(d)/math.cos(t/2-d)for t in ts))
 return r*r*(a-loss)

def solve(q,edges,faces,nfg=11):
 nf=len(faces);ne=len(edges);ee=[[tuple(sorted(e))for e in combinations(f,2)]for f in faces];inc=[[(f,ee[f].index(e))for f in range(nf)if e in ee[f]]for e in edges]
 iw=16;ip=iw+nf;ib=ip+3*nf;ie=ib+q;iff=ie+ne;N=iff+nf
 grid=np.linspace(0,math.pi,61);fg=np.linspace(0,math.pi,nfg);samples=[(ts,envelope(ts))for ts in product(fg,repeat=3)if sum(ts)<=2*math.pi+1e-12];M=2*q*len(grid)+nf*len(samples)+ne*(len(grid)+1);mat=lil_matrix((M,N));rhs=np.zeros(M);at=0
 for j in range(q):
  for t in grid:
   h=min(float(a)+float(k)*t for a,k in lines)
   mat[at,j]=-t;mat[at,14]=bv(t);mat[at,15]=h;mat[at,ib+j]=-1;rhs[at]=-fval(t,0);at+=1
   mat[at,j]=-t;mat[at,14]=An;mat[at,15]=h;mat[at,ib+j]=-1;rhs[at]=-cAn;at+=1
 for f in range(nf):
  for ts,A in samples:
   mat[at,iw+f]=A
   for k,t in enumerate(ts):mat[at,ip+3*f+k]=-t
   mat[at,iff+f]=-1;at+=1
 for k,(u,v)in enumerate(edges):
  for t in grid:
   a=r*r*math.sin(t);mat[at,u]=-t;mat[at,v]=-t
   for f,j in inc[k]:mat[at,iw+f]=-a;mat[at,ip+3*f+j]=t
   mat[at,ie+k]=-1;rhs[at]=-a;at+=1
  for f,j in inc[k]:mat[at,iw+f]=1
  rhs[at]=1;at+=1
 obj=np.r_[np.full(14,2*math.pi),-2*math.pi,-2*math.pi,np.zeros(4*nf),np.ones(q+ne+nf)]
 lp=linprog(obj,A_ub=mat.tocsr(),b_ub=rhs,bounds=[(None,None)]*14+[(0,None)]*2+[(0,1)]*nf+[(None,None)]*(3*nf+q+ne+nf),method='highs');assert lp.success
 return {'sampled_lp_not_bound':float(lp.fun-math.pi),'potentials':lp.x[:14].tolist(),'nu':float(lp.x[14]),'lambda':float(lp.x[15]),'weights':lp.x[iw:ip].tolist(),'face_potentials':lp.x[ip:ib].reshape(nf,3).tolist(),'face_supports':lp.x[iff:].tolist(),'grid_size':nfg}
if __name__=='__main__':
 start=time.time();G=json.loads((P/'stress-barycentric-result.json').read_text());faces=[x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});row=solve(10,edges,faces);row.update(family='candidate',index=-1);out=[row];print('candidate',row['sampled_lp_not_bound'],'seconds',time.time()-start,flush=True)
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());data=json.loads((P/'shared-radius-catalogue.json').read_text())['runs'];selected=[]
 for fam in ['10/4','11/3']:selected+=sorted([x for x in data if x['row']['family']==fam and x['certificate']['status']!='excluded'],key=lambda x:x['row']['sampled_lp_not_bound'])[:3]
 for test in selected:
  fam=test['row']['family'];idx=test['row']['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});row=solve(q,edges,faces);row.update(family=fam,index=idx,old_sampled_lp=test['row']['sampled_lp_not_bound']);out.append(row);print(fam,idx,row['sampled_lp_not_bound'],'old',row['old_sampled_lp'],'seconds',time.time()-start,flush=True)
 (P/'all-face-consistency-probe.json').write_text(json.dumps({'status':'numeric_only_sampled_factor_dual','runs':out},indent=2))
