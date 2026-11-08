import json
from decimal import Decimal,localcontext
from pathlib import Path
p=Path(__file__).resolve().parent
D=json.loads((p/'n25-inherited-certificate/geometry.json').read_text())
def q2(z):
 from fractions import Fraction
 def dec(a):
  f=Fraction(a); return Decimal(f.numerator)/Decimal(f.denominator)
 return dec(z[0])+dec(z[1])*Decimal(2).sqrt()
with localcontext() as ctx:
 ctx.prec=60
 a=((Decimal(2)-Decimal(2).sqrt())/3).sqrt()
 C=[[str((a*q2(v)).quantize(Decimal('1e-30'))) for v in point] for point in D['centers']]
 C.append(['0.0001','0'])
 (p/'n26-inherited-rational.json').write_text(json.dumps({'radius':'0.239146312','centers':C},indent=2)+'\n',encoding='utf8')
