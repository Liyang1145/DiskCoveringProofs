import math
from scipy.optimize import minimize_scalar
f=lambda x:x/2+1.5*x*math.sqrt(1-x*x/4)
z=minimize_scalar(lambda x:-f(x),bounds=(0,2),method='bounded')
print(z.x,f(z.x),'deficit',(3*math.sqrt(3)/4+1)-f(z.x))
