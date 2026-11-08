import math
from scipy.optimize import minimize_scalar
A=3*math.sqrt(3)/4
def f(s):
 h=math.sqrt(max(0,1-s*s/4));a=min(A,s*(1+h)/2)
 a=min(a,s*s/2 if s<math.sqrt(2) else math.sqrt(s*s-1))
 return a+s*h
z=minimize_scalar(lambda s:-f(s),bounds=(0,2),method='bounded',options={'xatol':1e-12});print(z.x,f(z.x),'deficit',A+1-f(z.x))
