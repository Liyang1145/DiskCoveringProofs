"""Positive-width near-merge capacity proof. Reuses audited interval primitives,
not saved conclusions: changes R and offset domain and ring count, then rechecks."""
import onehub_interval_certificate as K
from fractions import Fraction as F
from pathlib import Path
from mpmath import iv
import json,sys,time
DEL=F(sys.argv[1]) if len(sys.argv)>1 else F(1,20)
assert 4*K.Uq-1+2*DEL<1 and 2-4*K.Uq-DEL>DEL
R=K.U+K.Q(DEL);EM=3*K.U-1+K.Q(DEL)
def upper(d,B):
 z=K.box(*B[0]);ph=2*iv.pi*K.box(*B[1]);e=EM*K.box(*B[2])
 rho=K.rl+(K.rh-K.rl)*z;co=iv.cos(ph);si=iv.sin(ph)
 qa=(1+rho*rho-K.U*K.U)/(2*rho);al=K.acos01(qa);sa=iv.sqrt(K.clip01(1-qa*qa))
 wb=[K.Q(v) for v in d['boundary']];wh=[K.Q(v) for v in d['hub']]
 val=wb[0]*al+sa*(wb[1]*co+wb[2]*si)
 ell2=rho*rho+e*e-2*rho*e*co
 if ell2.a<=0:return None
 ell=iv.sqrt(ell2)
 if ell.a>= (R+K.U).b:return val
 qb=(R*R+ell2-K.U*K.U)/(2*R*ell)
 qb=iv.mpf([min(qb.a,iv.mpf(1)),min(qb.b,iv.mpf(1))])
 be=K.acos01(qb);sb=iv.sqrt(K.clip01(1-qb*qb))
 return val+wh[0]*be+sb*(wh[1]*(rho*co-e)/ell+wh[2]*rho*si/ell)
# Necessary10-ring capacity bound.
K.upper=upper
rows=[];start=time.time()
source=json.loads((K.P/'evidence/onehub-interval-all.json').read_text())['segments']
indices=list(range(12)) if len(sys.argv)<3 else [int(v) for v in sys.argv[2].split(',')]
for k in indices:
 s=source[k]
 d={v:[F(x) for x in s['weights'][v]] for v in ('boundary','hub')}
 row=K.verify_segment(d,F(k,12),F(k+1,12),maxboxes=250000,ring_count=10);rows.append(row)
 print(json.dumps({'delta':str(DEL),'segment':k,'boxes':row['boxes'],'seconds':time.time()-start}),flush=True)
 out={'status':'certified listed nearmerge segments','delta':str(DEL),'target_ring_count':10,'radius':str(K.Uq+DEL),'offset_max':str(3*K.Uq-1+DEL),'segments':rows}
 (K.P/'evidence'/('nearmerge-interval-'+str(DEL).replace('/','-')+('-tail' if len(indices)<12 else '')+'.json')).write_text(json.dumps(out,indent=2))
