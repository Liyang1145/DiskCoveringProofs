import json, numpy as np
from fractions import Fraction as F
d=json.load(open('/workspace/work/dcp-n11-lean/class33/data/q0_m2.json'))
S=d['sectors']
def coef(i): return {k:float(F(v)) for k,v in S[str(i)].items()}
def obj(c,a,u,v):
    q=u*u+v*v-2*u*v*np.cos(a); q=np.maximum(q,0)
    ch=np.sqrt(q); w=2*np.arcsin(np.minimum(1,0.19*ch))
    return (0.38**2/2)*u*v*np.sin(a)+(w-np.sin(w))/2 + c['C']*w - c['mu']*a - c['dL']*u*u - c['dR']*v*v - c['bL']*u - c['bR']*v
if __name__=='__main__':
    import math
    A=np.linspace(0,math.pi,401); U=np.linspace(0,1,201)
    a,u,v=np.meshgrid(A,U,U,indexing='ij')
    for i in range(9):
        c=coef(i); o=obj(c,a,u,v); k=np.unravel_index(o.argmax(),o.shape)
        print(i,o.max(),A[k[0]],U[k[1]],U[k[2]])
