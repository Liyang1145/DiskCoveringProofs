from fractions import Fraction as F
import json
from pathlib import Path
U=F('0.361102963744508672616920293904')
x=F(41,50); y=F(373,1000)
assert U<F(4,11)
assert x-x**3/6>F(8,11)
assert y-y**3/6>F(4,11)
# pi > 12 sin(pi/12)=3(sqrt6-sqrt2).
# Prove this exceeds 31/10: sqrt6-sqrt2>31/30
# 8-4sqrt3>961/900 iff sqrt3<6239/3600.
assert F(6239,3600)>0 and F(6239,3600)**2>3
assert x+6*y==F(1529,500)<F(31,10)
data={'level':'exact rational inequalities with stated analytic sine and inscribed-polygon lemmas','U_lt_4over11':True,'sin_lower_41over50_minus_8over11':str(x-x**3/6-F(8,11)),'sin_lower_373over1000_minus_4over11':str(y-y**3/6-F(4,11)),'sqrt3_upper_square_minus3':str(F(6239,3600)**2-3),'angle_sum_upper':str(x+6*y),'pi_lower':'31/10 via regular inscribed dodecagon'}
Path('research-2026/n12-global/evidence/rational-arc-controls.json').write_text(json.dumps(data,indent=2))
print(json.dumps(data))
