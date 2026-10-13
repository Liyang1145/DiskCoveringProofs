"""Independent exact polynomial calibration of stationary Taylor sign."""
import sympy as s
from pathlib import Path
import json
x,m=s.symbols('x m', real=True)
rows=[]
for a in [-3,-1,1,5]:
 f=s.Rational(a,2)*(x-s.Rational(87,40))**2+10
 mid=s.Rational(11,5);star=s.Rational(87,40)
 fm=f.subs(x,mid);fs=f.subs(x,star)
 corrected=fm-s.diff(f,x,2)*(mid-star)**2/2
 assert s.simplify(corrected-fs)==0
 rows.append({'a':a,'midvalue':str(fm),'stationaryvalue':str(fs),'codeexpression':str(corrected)})
Path(__file__).with_name('stationary_taylor_control.json').write_text(json.dumps(rows,indent=2))
print('4 exact polynomial controls: both curvature signs; PASS')
