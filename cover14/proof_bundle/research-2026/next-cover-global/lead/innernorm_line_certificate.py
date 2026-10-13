"""Exact tangent checks for innernorm-envelope line .135+.218alpha."""
from area_safe_certificate import I,Q,S,U,PI,L,asin,trig,P
import json
s=(1-I(U)**2).sqrt();x=I(Q('0.458'));sn,cs=trig(x);z=s*cs
assert 0<z.lo<z.hi<S
az=I(asin(Q(z.lo,S)).lo,asin(Q(z.hi,S)).hi,True)
a=x-PI/2+az+L/2
ap=1-s*sn/(1-z*z).sqrt();ab=a-x*ap
v=I(Q('1.77'));sn2,cs2=trig(v/2);z2=I(U)*sn2
b=2*I(asin(Q(z2.lo,S)).lo,asin(Q(z2.hi,S)).hi,True)
bp=I(U)*cs2/(1-z2*z2).sqrt();bb=b-v*bp
A=Q('0.135');k=Q('0.218')
checks={'a_intercept':I(A)-ab,'a_slope':I(k)-ap,'b_intercept':I(A)-bb,'b_slope':I(k)-bp,'a_tangent_at_pi':ab+PI*ap-L}
assert all(v.lo>0 for v in checks.values())
if __name__=='__main__':
 out={'status':'exact_interval_line_certificate','A':str(A),'k':str(k),'a_tangent':'0.458','b_tangent':'1.77','positive_margins':{key:val.dec()for key,val in checks.items()}}
 (P/'innernorm-line-certificate.json').write_text(json.dumps(out,indent=2));print({key:val.lo/S for key,val in checks.items()})
