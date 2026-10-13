"""Calibration exact trig identity, original ridge expression vs tangent split.
Point controls are numeric interval identities up to directed roundoff, not proof of continuum positivity.
"""
from pathlib import Path
import random,json,sympy as s
import ridge_tangent_jet as t
import patch_ridge_jet as old
from interval_joint_patch import I,iv,uf,lf
b,c=s.symbols('b c',real=True)
assert s.trigsimp(4*s.sin(b+c)*s.sin(b)*s.sin(c)-s.sin(2*b)-s.sin(2*c)+s.sin(2*(b+c)),method='fu')==0
rng=random.Random(867);rows=[]
for i in range(30):
 r,b1,b2,w1,w3=[I(str(x)) for x in [.379+rng.random()*.00099,1+rng.random()*.18,1+rng.random()*.18,.66+rng.random()*.1,.66+rng.random()*.1]]
 f=old.objective([r,b1,b2,b1-b2,w1,w3,2*r*iv.sin(b1+b2)]).v
 tangent=t.constant(r)+t.component([r,b1,w1],0)[0].v+t.component([r,b2,w3],1)[0].v
 T=b1+b2;gap=r*r*(-iv.sin(2*t.TAU)-2*iv.cos(2*t.TAU)*(T-t.TAU)+iv.sin(2*T))
 residual=tangent-f-gap
 assert residual.a<=0<=residual.b
 rows.append({'residual':str(residual),'tangent_gap':str(gap)})
Path(__file__).with_name('ridge_split_control.json').write_text(json.dumps({'sympy_trig_identity':True,'n':len(rows),'points':rows},indent=2));print('30 point identities; exact symbolic trig identity; PASS')
