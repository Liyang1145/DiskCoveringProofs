"""Recheck saved planes with exact symmetric cap, no new optimization."""
import json
from area_safe_certificate import I,Q,S,PI,U,asin,trig,P
A=2*asin(U/2);gA=A-I(U)*(1-I(U*U)/4).sqrt()
def verify(q,edges,row):
 t=list(map(Q,row['rational_angles']));y=list(map(Q,row['rational_potentials']));mu=Q(row['rational_mu']);assert mu>=0;bound=PI*(2*sum(y)-2*mu-1)
 for j,x in enumerate(t[:q]):
  sn,cs=trig(I(x));sh,ch=trig(I(x)/2);z=I(U)*sh;root=(1-z*z).sqrt();b=I(0)if x==0 else 2*I(asin(Q(z.lo,S)).lo,asin(Q(z.hi,S)).hi,True);bp=I(U)*ch/root
  val=I(U*U/2)*sn+(b-2*z*root)/2+mu*b
  der=I(U*U/2)*cs+(z*z+mu)*bp;slope=der-y[j];v1=val-I(x)*der+PI*I(max(0,slope.lo),max(0,slope.hi),True);c=gA/2+mu*A;v2=c-PI*y[j];bound+=I(max(v1.lo,c.lo,v2.lo),max(v1.hi,c.hi,v2.hi),True)
 for j,(u,v)in enumerate(edges):
  x=t[q+j];sn,cs=trig(I(x));slope=I(U*U)*cs-y[u]-y[v];bound+=I(U*U)*(sn-I(x)*cs)+PI*I(max(0,slope.lo),max(0,slope.hi),True)
 return bound
if __name__=='__main__':
 from itertools import combinations
 import math
 from scipy.optimize import brentq
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());G=json.loads((P/'stress-barycentric-result.json').read_text());rows=json.loads((P/'joint-boundary-probe.json').read_text())['runs'];out=[]
 for row in rows:
  fam=row['family'];q=10 if fam=='candidate' else int(fam.split('/')[0]);idx=row['index'];faces=([x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]])if fam=='candidate'else(D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces']);edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=dict(row);ts=rec['rational_angles'][:];rn=float(U);mn=float(Q(row['rational_mu']));ys=list(map(float,map(Q,row['rational_potentials'])))
  for j in range(q):
   def fn(t):
    z=rn*math.sin(t/2);bp=rn*math.cos(t/2)/math.sqrt(1-z*z);return rn*rn/2*math.cos(t)+(z*z+mn)*bp-ys[j]
   tt=0 if fn(0)<=0 else(math.pi if fn(math.pi)>=0 else brentq(fn,0,math.pi));ts[j]=str(max(Q(0),min(Q('3.141592653589'),Q(format(tt,'.12f')))))
  rec['rational_angles']=ts;b=verify(q,edges,rec);rec.update(status='excluded'if b.hi<0 else'inconclusive',upper_display=b.hi/S,upper_exact=str(Q(b.hi,S)));out.append(rec);print(fam,idx,rec['status'],rec['upper_display'],flush=True)
 (P/'joint-boundary-exact-cap-probe.json').write_text(json.dumps({'status':'exact_interval_bounds_analytic_concavity','runs':out},indent=2))
