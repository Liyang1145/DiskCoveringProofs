import sympy as S,json
from interval_joint_patch import P
b1,b2,A,B=S.symbols('b1 b2 A B',real=True);T=b1+b2;D=b1-b2
X1=(S.sin(2*b1)+S.sin(2*A)-S.sin(2*b2))/2;Y1=S.sin(b2)**2+(S.cos(2*A)-S.cos(2*b1))/2
X2=(S.sin(2*b2)+S.sin(2*B)-S.sin(2*b1))/2;Y2=S.sin(b1)**2-(S.cos(2*b2)-S.cos(2*B))/2
for expr in [X1-S.sin(A)*S.cos(A)-S.cos(T)*S.sin(D),Y1-S.cos(A)**2+S.cos(T)*S.cos(D),X2-S.sin(B)*S.cos(B)+S.cos(T)*S.sin(D),Y2-S.cos(B)**2+S.cos(T)*S.cos(D)]:assert S.trigsimp(S.expand_trig(expr))==0
(P/'face_complement_exact_control.json').write_text(json.dumps({'four_sourcecomponentidentities':True,'coincidentbranch':'A,B>0,A+B=pi/2 => othernorm=cosA,angle=pi/2-A'},indent=2));print('4 exact sourcecomponent identities PASS')
