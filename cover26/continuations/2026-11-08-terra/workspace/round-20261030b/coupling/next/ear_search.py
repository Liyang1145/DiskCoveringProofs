from scipy.optimize import differential_evolution
import math
A=3*math.sqrt(3)/4
def f(z):
 x,y=z
 return min(A,x*y/2) + .5*x*math.sqrt(max(0,1-x*x/4)) + .5*y*math.sqrt(max(0,1-y*y/4))
z=differential_evolution(lambda x:-f(x),[(0,2),(0,2)],tol=1e-12);print(z.x,f(z.x),'defect',A+1-f(z.x))
