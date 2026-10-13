"""Uniform rigorous high-bearing hubsubharmonicity bound, exactcoefficients."""
from pathlib import Path
import json,hashlib
from interval_joint_patch import I,iv,R,z,pi
P=Path(__file__).parent
c1=z[78]/(2*R);c2=-z[82]/(2*R);B=(-z[16]+z[20])/(4*R*R)
a=-iv.cos(I(2));assert a.a>0 and a.b<1
# d>=4r sin²1, d-u>=2r a. Reciprocalcap atsmallestr=3/8.
cap=I(max((c1/a+c2).b,(c1+c2/a).b))/(I(3)/4)
lower=4*B-cap;assert lower.a>I('.39').b
# Neighborcenter modulus>|1-r| for b>=1, rrange.
r=I('.375','.38');s=iv.sqrt(1-r*r)
# cn-(1-r)^2=2r(1-s sin2b-r cos2b) = 2r(1-cos(2b-asinr)) positive; simply |c|≥ verticalcomponent2r sin²b.
normgap=I(3)/4*iv.sin(I(1))**2-I(5)/8
# verticalcomponentalone notenough; exact c² formula, minimumx0=2-acos(.375).
x0=I(2)-iv.atan2(iv.sqrt(1-I('.375')**2),I('.375'))
# c²-(1-r)^2=2r(1-cosx0), x0=2b-acosr, positive onentireb>=1range
normsqgap=I(3)/4*(1-iv.cos(x0));assert normsqgap.a>0
out={'scope':'allr[3/8,19/50],b1,b2in[1,acosr],alllegalC848hubpoints','DeltaF_lower':str(lower),'c1':str(c1),'c2':str(c2),'4sum_beta':str(4*B),'reciprocal_upper':str(cap),'a_minuscos2':str(a),'neighbor_norm_squared_gap_lower':str(normsqgap),'coefficient_sha256':hashlib.sha256((P/'joint_nested_frozen.json').read_bytes()).hexdigest()};(P/'hub_laplacian_certificate.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
