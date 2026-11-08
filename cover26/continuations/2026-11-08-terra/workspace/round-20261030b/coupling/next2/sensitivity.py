import math
from scipy.optimize import brentq
b=17
for defect in [.0265,.027]:
 def f(r):
  t=math.pi/b;g=t-math.sin(t)*math.cos(t)+math.sin(t)*math.sqrt(r*r-math.sin(t)**2)
  return (50-b)*3*math.sqrt(3)/4*r*r+b*r*r/2+b*g-defect*b*r*r-math.pi
 print(defect,brentq(f,.228,.229))
