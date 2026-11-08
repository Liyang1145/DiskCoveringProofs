"""Numerical proposals only: shared-edge groups with preferred triangle angles."""
import math,json
from scipy.optimize import differential_evolution
d=math.pi/3
shift=.06
def H(x):
    x=abs(x)
    return x*x if x<=.2 else .4*x-.04
for group in [1,2]:
    cap=1.7604 if group==1 else 2.206
    target=[d+shift,d+shift,d-2*shift] if group==1 else [d-shift,d-shift,d+2*shift]
    def evaluate(z):
        gamma=math.pi*z[0];alpha=(math.pi-gamma)*z[1];beta=math.pi-alpha-gamma;R=z[2]
        sa,sb,sg=map(math.sin,[alpha,beta,gamma])
        area=2*R*R*sa*sb*sg
        def switch(s):return R*s*math.sqrt(max(0,1-R*R*s*s))
        value=area+switch(sg) if group==1 else area+switch(sa)+switch(sb)
        penalty=sum(H(x-y) for x,y in zip([alpha,beta,gamma],target))
        return value,penalty,[alpha,beta,gamma,R]
    def ratio(z):
        value,penalty,_=evaluate(z)
        return (cap-value)/penalty if penalty>1e-12 else 1e3
    ans=differential_evolution(ratio,[(1e-7,1-1e-7),(1e-7,1-1e-7),(1e-7,1)],seed=1,tol=1e-10,maxiter=1000)
    print(json.dumps({'group':group,'ratio_proposal':ans.fun,'args':evaluate(ans.x)}),flush=True)
