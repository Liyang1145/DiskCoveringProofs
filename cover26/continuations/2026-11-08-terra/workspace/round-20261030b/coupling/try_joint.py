from scipy.optimize import minimize_scalar
import math
f=lambda x:x/2+x*math.sqrt(1-x*x/4)
z=minimize_scalar(lambda x:-f(x),bounds=(0,2),method='bounded');print(z.x,f(z.x),.5+3*math.sqrt(3)/4,(.5+3*math.sqrt(3)/4)-f(z.x))
