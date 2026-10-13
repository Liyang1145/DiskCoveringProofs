import sympy as S,json
from pathlib import Path
v,t,r,b1,b2,ss=S.symbols('v t r b1 b2 s',real=True)
E1=(v-r*S.sin(2*b1))**2+(t+r*S.cos(2*b1))**2-r*r
E2=(v-r*S.sin(2*b2))**2+(t-r*S.cos(2*b2))**2-r*r
assert S.trigsimp(S.expand(E1)-(v*v+t*t-2*r*(v*S.sin(2*b1)-t*S.cos(2*b1))))==0
assert S.trigsimp(S.expand(E2)-(v*v+t*t-2*r*(v*S.sin(2*b2)+t*S.cos(2*b2))))==0
T=b1+b2;D=b1-b2;sub={v:2*r*S.sin(T)*S.cos(D),t:2*r*S.sin(T)*S.sin(D)}
assert S.trigsimp(S.expand_trig(E1.subs(sub)))==0
assert S.trigsimp(S.expand_trig(E2.subs(sub)))==0
# circlecenterdifference² =4r²cos²T
cd=r*r*((S.sin(2*b1)-S.sin(2*b2))**2+(S.cos(2*b1)+S.cos(2*b2))**2)
assert S.trigsimp(S.expand_trig(cd-4*r*r*S.cos(T)**2))==0
out={'disk_completion':True,'ridge_onbothcircles':True,'center_separation_squared':'4r²cos²T','degeneracy':'T=pi/2 facecirclescoincide','scope':'exactalgebra'};Path(__file__).with_name('cartesian_hub_control.json').write_text(json.dumps(out,indent=2));print(out)
