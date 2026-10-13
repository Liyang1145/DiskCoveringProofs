import sympy as S,json
from interval_joint_patch import P
r,s,u=S.symbols('r s u',real=True);d2=1-2*s*r*u
num=S.expand(d2-(1-s*u)**2-u*(2*s*(1-r)-s*s*u));assert num==0
b1,b2,de=S.symbols('b1 b2 de',real=True)
assert S.trigsimp(S.expand_trig(S.sin(2*b1-de)-S.sin(2*b2+de)-2*S.cos(b1+b2)*S.sin(b1-b2-de)))==0
b,A=S.symbols('b A',real=True)
# saturated face Cartesian source vector = 2r sinA*(cosA,sinA)
v=r*(S.sin(2*b)+S.sin(2*A));t=r*(S.cos(2*A)-S.cos(2*b));X=v-r*S.sin(2*b);Y=2*r*S.sin(b)**2-t
assert S.trigsimp(X-2*r*S.sin(A)*S.cos(A))==0
assert S.trigsimp(Y-2*r*S.sin(A)**2)==0
(P/'corner_identity_control.json').write_text(json.dumps({'h2_factored_numerator_identity':True,'opposite_face_cap_difference_identity':True,'saturated_source_vector_identity':True,'branch_condition':'legal A in(0,pi); sourcevectorpositivefactor2rsinA so phi=A,e=rsinA/R0'},indent=2));print('3 symbolic corner identities PASS')
