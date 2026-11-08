import math
from scipy.optimize import minimize_scalar
r=.23;b=17;d=math.pi/b;s=math.sin(d);c=math.cos(d);h=math.sqrt(r*r-s*s);L=2*(c-h)*s;M=.5+3*math.sqrt(3)/4
f=lambda x:x/2+x*math.sqrt(max(0,1-x*x/4))
xstar=1.610301410986
loss=lambda z:s*z+.5*r*r*(M-f(min(xstar,(L+2*r*z/s)/r)))
a=minimize_scalar(loss,bounds=(0,h),method='bounded',options={'xatol':1e-14});print('z',a.x,'perloss',a.fun,'times17',a.fun*17,'required_excess approx .078944')
