import math,numpy as np
from scipy.optimize import differential_evolution
# One ear triangle vertices are inside unit disk. Its two connectors obey lens bounds.
def value(z):
 p=np.array(z).reshape(3,2)
 if any(float(q@q)>1 for q in p):return 0
 x=np.linalg.norm(p[1]-p[0]);y=np.linalg.norm(p[2]-p[0]);area=abs(np.linalg.det(np.stack((p[1]-p[0],p[2]-p[0]))))/2
 g=lambda t:t*math.sqrt(max(0,1-t*t/4))/2
 return area+g(x)+g(y)
z=differential_evolution(lambda z:-value(z),[(-1,1)]*6,popsize=15,maxiter=800,tol=1e-7,seed=5); print('objective',-z.fun,'points',z.x,'norms',np.linalg.norm(z.x.reshape(3,2),axis=1),'strictly numerical only')
