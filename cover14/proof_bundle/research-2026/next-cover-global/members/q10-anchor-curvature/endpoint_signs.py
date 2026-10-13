"""Bounded exact-interval endpoint transversality control, not a curvature sample.
Read-only source imports; run python -B. All output stays next to this script.
"""
import sys,json,hashlib
from pathlib import Path
P=Path(__file__).resolve().parent
L=P.parents[1]/'lead'
sys.dont_write_bytecode=True
sys.path.insert(0,str(L))
from root_integer_certificate import I,Q,S,calibrate
calibrate()
source=L/'root-integer-certificate.json'
cert=json.loads(source.read_text())
z,c,r=[I(int(Q(a)*S),int(Q(b)*S),True) for a,b in cert['box_dyadic']]
s=(1-r*r).sqrt();a=(s+z)/2;t=r+(r*r-z*z).sqrt()
b=r+(r*r-(a-z)**2).sqrt();d=1-(r*r-c*c).sqrt()
C=[(sx*a,sy*b) for sx in(-1,1) for sy in(-1,1)]+[(sx*c,sy*d) for sx in(-1,1) for sy in(-1,1)]+[(s,I(0)),(-s,I(0)),(z,I(0)),(-z,I(0)),(I(0),t),(I(0),-t)]
v1=(1+a*a+b*b-r*r)/2;v2=(1+c*c+d*d-r*r)/2;det=a*d-b*c
px=(v1*d-v2*b)/det;py=(a*v2-c*v1)/det
A=[(s,r),(px,py),(I(0),I(1)),(-px,py),(-s,r),(-s,-r),(-px,-py),(I(0),I(-1)),(px,-py),(s,-r)]
owners=[3,7,5,1,9,0,4,6,2,8] # root_cover_check.py order, NOT local SOSC order
rows=[]
for j,p in enumerate(A):
    for side,k in [('preceding',owners[(j-1)%10]),('following',owners[j])]:
        qprime=2*(C[k][0]*p[1]-C[k][1]*p[0])
        signed=qprime if side=='preceding' else -qprime
        assert signed.lo>Q(1,5)*S,(j,k,qprime.dec())
        rows.append(dict(anchor=j,site=k,side=side,derivative_interval=qprime.dec()))
out=dict(status='proved_interval_endpoint_signs_conditional_on_C1167',scope='20 literal root boundary incidences only; both signed slopes >1/5; no neighborhood size or convexity certification',sources={str(p.relative_to(P.parents[1])):hashlib.sha256(p.read_bytes()).hexdigest() for p in [source,L/'root_integer_certificate.py',L/'root_cover_check.py']},kernel='shared lead directed dyadic interval kernel, calibrated; not independent kernel',rows=rows)
(P/'endpoint-signs.json').write_text(json.dumps(out,indent=2))
print('20 endpoint derivative signs proved, signed lower > 1/5; output endpoint-signs.json')
