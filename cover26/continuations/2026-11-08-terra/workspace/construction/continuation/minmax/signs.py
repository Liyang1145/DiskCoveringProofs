from pathlib import Path
import json,math
from fractions import Fraction as F
p=Path(__file__).parent; d=json.loads((p/'rational_geometry.json').read_text());C=[tuple(map(F,x)) for x in d['centers']];Q=[tuple(map(F,x)) for x in d['boundary_anchors']]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def sub(a,b):return a[0]-b[0],a[1]-b[1]
for i in range(16):
 q0=Q[(i-1)%16];q1=Q[i];c=C[i];print(i, float(cross(sub(q1,q0),sub(c,q0))))
