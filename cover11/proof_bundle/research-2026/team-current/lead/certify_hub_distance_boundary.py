from pathlib import Path
import json,hashlib
from interval_joint_patch import I,R,z
P=Path(__file__).parent;c1=z[78]/(2*R);c2=-z[82]/(2*R);a=I(19)/50;lap=(-z[16]+z[20])/(R*R);cap=I(max((c1/a+c2).b,(c1+c2/a).b))*I(4)/3;lower=lap-cap;assert lower.a>I('.0476').b
out={'scope':'legalC848r[3/8,19/50],d/(2r)>=69/50; d=|Q1-Q2|','laplacian_lower':str(lower),'distance_lower':'.285','coefficient_sha256':hashlib.sha256((P/'joint_nested_frozen.json').read_bytes()).hexdigest()};(P/'hub_distance_boundary_certificate.json').write_text(json.dumps(out,indent=2));print(out)
