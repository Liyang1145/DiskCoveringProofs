"""One bounded high-precision root calibration of the newly derived D3 contact chart.
Numerical only: tests formula consistency, not existence/uniqueness or coverage."""
from pathlib import Path
import sympy as S
import mpmath as mp
import json
mp.mp.dps=65
a,t,r,w=S.symbols('a t r w')
b=(1+a+r)/2
F=t*t-2*t*r-a*t+a*r+a*a
G=(1+t*t-r*r)*(3*b*b+w*w)-t*(3*b*b-w*w+6*b*w)
H=4*w*w-12*r*r+3*(1-a-r)**2
M=S.Matrix([F,G,H]).jacobian([a,t,w])
J=S.factor(M.det())
fun=S.lambdify((a,t,r,w),(F,G,H,J),'mpmath')
root=mp.findroot(fun,(mp.mpf('.27824'),mp.mpf('.76917'),mp.mpf('.361103'),mp.mpf('.5418')),tol=mp.mpf('1e-58'),maxsteps=25)
vals=[str(x) for x in root]
res=[str(x) for x in fun(*root)]
out={'level':'numeric only; one chart calibration','vars':['a','t','r','w'],'root':vals,'residual':res,'F':str(F),'G':str(S.expand(G)),'H':str(H),'J':str(J)}
p=Path(__file__).resolve().parents[1]/'evidence'/'d3-chart-calibration.json'
p.write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps({'root':vals,'max_residual':str(max(abs(x) for x in fun(*root))),'path':str(p)}))
