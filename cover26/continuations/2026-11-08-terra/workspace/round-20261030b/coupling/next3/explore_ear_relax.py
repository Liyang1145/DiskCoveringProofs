from scipy.optimize import differential_evolution
import math
A=3*math.sqrt(3)/4
def f(z):
 x,y=z; hx=math.sqrt(max(0,1-x*x/4));hy=math.sqrt(max(0,1-y*y/4));return min(A,x*y/2,x*(1+hx)/2,y*(1+hy)/2)+x*hx/2+y*hy/2
z=differential_evolution(lambda x:-f(x),[(0,2),(0,2)],tol=1e-10);print(z.x,'total',f(z.x),'deficit',A+1-f(z.x))
