import math
from scipy.optimize import minimize
r=.234700091;a=(math.cos(.4488)-1,-math.sin(.4488));f=lambda v:2*v[0]*v[1]
cons=[{'type':'ineq','fun':lambda v:r*r-v[0]**2-v[1]**2},{'type':'ineq','fun':lambda v:r*r-(v[0]-a[0])**2-(v[1]-a[1])**2},{'type':'ineq','fun':lambda v:1-(1+v[0])**2-v[1]**2}]
z=minimize(lambda v:-f(v),[-.11,-.19],constraints=cons,method='SLSQP',options={'ftol':1e-13});print(z.x,z.fun,z.success,[i['fun'](z.x) for i in cons])
