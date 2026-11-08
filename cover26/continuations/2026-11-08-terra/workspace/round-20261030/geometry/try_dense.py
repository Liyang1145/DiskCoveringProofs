import sys
from fractions import Fraction as F
sys.path.insert(0,'research-2026/n26-terra/round-20261030/geometry')
import lens_polygon as l
v=set()
for k in range(17):
 t=F(k,16); x=(1-t*t)/(1+t*t);y=2*t/(1+t*t)
 for sx in (-1,1):
  for sy in (-1,1):v.add((sx*x,sy*y))
l.D=sorted(v)
for n in (2365,2368,2369):
 z=l.bound(F(n,10000),F(237,1000),F(n,10000),F(237,1000));print(n,len(v),float(z),z<F(1,25))


