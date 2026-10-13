"""All-face fractional hexagon caps; sampled LP proposes, exact tangent certifies."""
from joint_innernorm_probe import *
import time

def solve(q,edges,faces):
 nf=len(faces);ne=len(edges);N=16+nf+q+ne;grid=np.linspace(0,math.pi,81);M=2*q*len(grid)+ne*len(grid)+ne;mat=lil_matrix((M,N));rhs=np.zeros(M);at=0;inc=[[j for j,f in enumerate(faces)if all(v in f for v in e)]for e in edges]
 for j in range(q):
  for t in grid:
   h=min(float(a)+float(k)*t for a,k in lines)
   mat[at,j]=-t;mat[at,14]=bv(t);mat[at,15]=h;mat[at,16+nf+j]=-1;rhs[at]=-fval(t,0);at+=1
   mat[at,j]=-t;mat[at,14]=An;mat[at,15]=h;mat[at,16+nf+j]=-1;rhs[at]=-cAn;at+=1
 for k,(u,v)in enumerate(edges):
  for t in grid:
   a=r*r*math.sin(t);mat[at,u]=-t;mat[at,v]=-t
   for f in inc[k]:mat[at,16+f]=-a
   mat[at,16+nf+q+k]=-1;rhs[at]=-a;at+=1
  for f in inc[k]:mat[at,16+f]=1
  rhs[at]=1;at+=1
 obj=np.r_[np.full(14,2*math.pi),-2*math.pi,-2*math.pi,np.full(nf,3*math.sqrt(3)/2*r*r),np.ones(q+ne)]
 lp=linprog(obj,A_ub=mat.tocsr(),b_ub=rhs,bounds=[(None,None)]*14+[(0,None)]*2+[(0,1)]*nf+[(None,None)]*(q+ne),method='highs');assert lp.success
 y=[Q(format(v,'.12f'))for v in lp.x[:14]];nu=max(Q(0),Q(format(lp.x[14],'.12f')));lam=max(Q(0),Q(format(lp.x[15],'.12f')))
 # Floor cap weights: keeps nonnegativity and all edge capacities exactly.
 weights=[Q(math.floor(max(0,v)*10**12),10**12)for v in lp.x[16:16+nf]];assert all(sum(weights[f]for f in ii)<=1 for ii in inc)
 ts=[]
 for j in range(q):
  pts=[0,float((verts[1][0].lo+verts[1][0].hi)/(2*S)),float((verts[2][0].lo+verts[2][0].hi)/(2*S)),math.pi];cand=list(pts)
  for seg in range(3):
   slope=float(lines[seg][1]);g=lambda t:fn(t,float(nu))+float(lam)*slope-float(y[j]);lo,hi=pts[seg],pts[seg+1]
   if g(lo)>0 and g(hi)<0:cand.append(brentq(g,lo,hi))
  t=max(cand,key=lambda t:fval(t,float(nu))+float(lam)*min(float(a)+float(k)*t for a,k in lines)-float(y[j])*t);ts.append(max(Q(0),min(Q('3.141592653589'),Q(format(t,'.12f')))))
 for k,(u,v)in enumerate(edges):
  coeff=float(U*U*(1-sum(weights[f]for f in inc[k])));pot=float(y[u]+y[v]);t=0 if pot>=coeff else(math.pi if pot<=-coeff else math.acos(pot/coeff));ts.append(max(Q(0),min(Q('3.141592653589'),Q(format(t,'.12f')))))
 row={'rational_angles':list(map(str,ts)),'rational_potentials':list(map(str,y)),'rational_nu':str(nu),'rational_lambda':str(lam),'rational_face_weights':list(map(str,weights)),'sampled_lp_not_bound':float(lp.fun-math.pi)}
 bound=certify(q,edges,faces,row);row.update(status='excluded'if bound.hi<0 else'inconclusive',upper_display=bound.hi/S,upper_exact=str(Q(bound.hi,S)));return row

def certify(q,edges,faces,row):
 t=list(map(Q,row['rational_angles']));y=list(map(Q,row['rational_potentials']));nu=Q(row['rational_nu']);lam=Q(row['rational_lambda']);weights=list(map(Q,row['rational_face_weights']));assert len(weights)==len(faces)and all(w>=0 for w in weights)
 # Reuse exact boundary support via zero-edge invocation, then add new edges.
 b=verify(q,[],t[:q],y,nu,lam)+I(3).sqrt()*(3*U*U/2)*sum(weights)
 for k,(u,v)in enumerate(edges):
  w=sum(weights[f]for f,ids in enumerate(faces)if u in ids and v in ids);assert w<=1;a=U*U*(1-w);x=t[q+k];assert 0<=x and I(x).hi<PI.lo;sn,cs=trig(I(x));slope=a*cs-y[u]-y[v];b+=a*(sn-I(x)*cs)+PI*I(max(0,slope.lo),max(0,slope.hi),True)
 return b
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());G=json.loads((P/'stress-barycentric-result.json').read_text());faces=[x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=solve(10,edges,faces);assert rec['status']!='excluded';rec.update(family='candidate',index=-1);out=[rec];print('candidate',rec['upper_display'],flush=True)
 data=json.loads((P/'shared-radius-catalogue.json').read_text())['runs'];selected=[]
 for fam in ['10/4','11/3']:
  selected+=sorted([x for x in data if x['row']['family']==fam and x['certificate']['status']!='excluded'],key=lambda x:x['row']['sampled_lp_not_bound'])[:6]
 for test in selected:
  fam=test['row']['family'];idx=test['row']['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=solve(q,edges,faces);rec.update(family=fam,index=idx);out.append(rec);print(fam,idx,rec['status'],rec['upper_display'],flush=True)
 (P/'hexagon-dual-probe.json').write_text(json.dumps({'status':'bounded_interval_hexagon_fractional_dual','runs':out},indent=2))
