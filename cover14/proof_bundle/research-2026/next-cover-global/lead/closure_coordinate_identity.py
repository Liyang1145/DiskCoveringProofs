"""Exact symbolic kernel checks for coordinate proof, not a continuum certificate by sampling."""
import sympy as s
import json
from pathlib import Path
p,m,d,a,L,t=s.symbols('psi m d a L theta',real=True)
w=lambda x:s.Matrix([-s.cos(x),s.sin(x)])
expr=L*w(p).dot(a*(w(m+d)-w(m-d)))-2*a*L*s.sin(p-m)*s.sin(d)
assert s.trigsimp(s.expand_trig(expr))==0
expr2=w(m-d)+w(m+d)-2*s.cos(d)*w(m)
assert all(s.trigsimp(s.expand_trig(x))==0 for x in expr2)
# Chord components, exact identities, positive scale 2sin(theta/2).
prev=s.Matrix([s.cos(t)-1,-s.sin(t)])-2*s.sin(t/2)*w(-s.pi/2+t/2)
nxt=s.Matrix([s.cos(t)-1,s.sin(t)])-2*s.sin(t/2)*w(s.pi/2-t/2)
assert all(s.trigsimp(s.expand_trig(x))==0 for x in list(prev)+list(nxt))
P=Path(__file__).resolve().parent
(P/'closure-coordinate-identity.json').write_text(json.dumps({'status':'exact_symbolic_identity_checks','dot_halfplane_identity':True,'bisector_sum_identity':True,'chord_direction_identities':True,'scope':'Algebra only; sign/domain argument in CLOSURE-COORDINATE-PROOF.md.'},indent=2))
print('Exact dotproduct, bisector and chord direction identities verified.')
