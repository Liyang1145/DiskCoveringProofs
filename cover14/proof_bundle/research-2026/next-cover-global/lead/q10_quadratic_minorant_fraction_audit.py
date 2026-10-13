"""Independent directed Fraction replay of large-box quadratic minorant."""
import q10_adaptive_flow_fraction_audit as f
import json,hashlib
from fractions import Fraction as Q
P=f.P;src=P/'q10-quadratic-minorant-certificate.json';a=json.loads(src.read_text());eps=Q(a['epsilon']);U=Q(a['U']);kap=Q(a['kappa']);pen=Q(a['penalty']);z=[[Q(x)for x in e]for e in a['flow']];T=[[[Q(x)for x in rr]for rr in e]for e in a['jet']];V=[[Q(x)for x in rr]for rr in a['V']];caps=[[Q(x)for x in c]for c in a['caps']]
assert z==f.z and T==[[[x/4 for x in rr]for rr in e]for e in f.T]and a['edges']==[k for k,e in f.core];assert list(map(Q,a['theta0']))==f.th
assert caps==[[Q(int(i==5)-int(i==4))for i in range(10)],[Q(int(i==0)-int(i==9))for i in range(10)]]
assert all(sum(V[i][j]for i in range(10))==0 for j in range(9))
M=[rr[:]for rr in V[:9]]
for j in range(9):
 k=next(k for k in range(j,9)if M[k][j]);M[j],M[k]=M[k],M[j];q=M[j][j];M[j]=[x/q for x in M[j]]
 for k in range(j+1,9):
  q=M[k][j];M[k]=[x-q*y for x,y in zip(M[k],M[j])]
p=f.pt;add=f.add;sub=f.sub;mul=f.mul;div=f.div;sqrt=f.sqrt;sm=f.summ
H=[[p(pen*sum(c[i]*c[j]for c in caps))for j in range(10)]for i in range(10)];g=[p(0)for _ in range(10)];f0=p(0);lowers=[]
for e,(_,edge)in enumerate(f.core):
 n=sqrt(p(sum(x*x for x in z[e])));u=[div(p(x),n)for x in z[e]];along=[sm(mul(u[k],p(T[e][k][i]))for k in range(2))for i in range(10)];lower=n[0]-eps*sum(max(abs(x[0]),abs(x[1]))for x in along);assert lower>0;lowers.append(lower)
 perp=[sub(mul(u[0],p(T[e][1][i])),mul(u[1],p(T[e][0][i])))for i in range(10)]
 f0=sub(f0,mul(p(U),n))
 for i in range(10):
  g[i]=sub(g[i],mul(p(U),along[i]))
  for j in range(10):H[i][j]=sub(H[i][j],mul(p(U/lower),mul(perp[i],perp[j])))
 b=edge[2]
 if b is not None:
  aa=f.Ac[b];der=[aa[1],f.neg(aa[0])];mix=[sm(mul(der[k],p(T[e][k][i]))for k in range(2))for i in range(10)]
  wbound=mul(p(eps),sqrt(p(sum(sum(map(abs,T[e][k]))**2 for k in range(2)))))
  H[b][b]=add(H[b][b],sub(sub(sm(mul(aa[k],p(z[e][k]))for k in range(2)),mul(n,p(eps/3))),wbound))
  for i in range(10):H[b][i]=add(H[b][i],mix[i]);H[i][b]=add(H[i][b],mix[i])
  f0=sub(f0,sm(mul(aa[k],p(z[e][k]))for k in range(2)))
  for i in range(10):g[i]=sub(g[i],sm(mul(aa[k],p(T[e][k][i]))for k in range(2)))
  g[b]=add(g[b],sm(mul(der[k],p(z[e][k]))for k in range(2)))
HH=[[sm(mul(p(V[k][i]*V[l][j]),sub(H[k][l],p(kap*int(k==l))))for k in range(10)for l in range(10))for j in range(9)]for i in range(9)]
bound=max(sum(max(abs(lo-int(i==j)),abs(hi-int(i==j)))for j,(lo,hi)in enumerate(rr))for i,rr in enumerate(HH));assert bound<1
out=dict(status='fraction_quadratic_minorant_replay',source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),epsilon=str(eps),kappa=str(kap),penalty=str(pen),row_bound=str(bound),row_bound_display=float(bound),min_radial_lower=str(min(lowers)),f0=list(map(str,f0)),gradient=[list(map(str,x))for x in g],scope='Exactbalancedflow/rank/incidence checked; independently rounded quadraticmatrix andtrig. Analyticminorant lemma separate.')
(P/'q10-quadratic-minorant-fraction-audit.json').write_text(json.dumps(out,indent=2));print(out['status'],float(bound),float(min(lowers)))
