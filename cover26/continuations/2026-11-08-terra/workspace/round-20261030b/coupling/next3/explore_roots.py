import math
from scipy.optimize import brentq
for b in range(14,27):
 def f(r):
  t=math.pi/b;g=t-math.sin(t)*math.cos(t)+math.sin(t)*math.sqrt(r*r-math.sin(t)**2)
  return (50-b)*3*math.sqrt(3)/4*r*r+b*r*r/2+b*g-(59/2000)*b*r*r-math.pi
 if f(.23)>0:print(b,brentq(f,.228,.23))
 else:print(b,'> .23')
