import math
from scipy.optimize import brentq
for b in range(14,27):
 def excess(r):
  t=math.pi/b;g=t-math.sin(t)*math.cos(t)+math.sin(t)*math.sqrt(r*r-math.sin(t)**2)
  return (50-b)*3*math.sqrt(3)/4*r*r+b*r*r/2+b*g-(53/2000)*b*r*r-math.pi
 if excess(.23)>0:print(b,brentq(excess,.2278,.23))
 else:print(b,'> .23')
