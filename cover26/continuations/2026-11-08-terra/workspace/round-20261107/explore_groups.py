"""Numerical proposals only; no result from this script is a certificate."""
import math
import sys
import os
from scipy.optimize import differential_evolution, minimize_scalar

U = float(sys.argv[1]) if len(sys.argv)>1 else .229
A = 3*math.sqrt(3)/4
BASE = A+.5-147325/83694
EAR = A+1-math.sqrt(9/4+1.5*math.sqrt(3))
XMAX = math.sqrt((15+math.sqrt(33))/8)  # f'(x)=0
SMAX = 2+2*math.sqrt(3)

def f(x):
    x=min(max(x,0),XMAX)
    return x/2+x*math.sqrt(1-x*x/4)

def H(s):
    s=min(max(s,0),SMAX)
    return (s/4+math.sqrt(s*(8-s))/4 if s<=4
            else (s+4)*math.sqrt(s*(8-s))/16)

def run(b):
    d=math.pi/b
    anchor=d-float(os.environ.get('FAN_SHIFT','0'))
    def G(t):
        s=math.sin(t)
        return t-s*math.cos(t)+s*math.sqrt(max(0,U*U-s*s))
    sd=math.sin(anchor)
    slope=2*sd*sd+math.cos(anchor)*(U*U-2*sd*sd)/math.sqrt(U*U-sd*sd)
    def data(t):
        s=math.sin(t)
        a=math.cos(t)-math.sqrt(max(0,U*U-s*s))
        J=max(0,G(anchor)+slope*(t-anchor)-G(t))
        return s,a,J
    def edge(t,u,dt,du):
        return math.sqrt((dt[1]-du[1])**2+4*dt[1]*du[1]*math.sin((t+u)/2)**2)/U
    def single(x):
        t,u,v=x
        dt,du=data(t),data(u)
        ell=edge(t,u,dt,du)+v/min(dt[0],du[0])**2
        return max(BASE,A+.5-f(ell))+(dt[2]+du[2]+v)/(2*U*U)
    def ear(x):
        t,u,v,p,q,w=x
        ds=[data(z) for z in [t,u,v]]
        x1=edge(t,u,ds[0],ds[1])+p/ds[0][0]**2+q/ds[1][0]**2
        x2=edge(u,v,ds[1],ds[2])+q/ds[1][0]**2+w/ds[2][0]**2
        return max(EAR,A+1-H(x1*x1+x2*x2))+(.5*(ds[0][2]+ds[2][2]+p+w)+ds[1][2]+q)/(U*U)
    angles=[(max(.0001,d-.08),min(math.asin(U)-1e-8,d+.08))]
    r1=differential_evolution(single,angles*2+[(0,.006)],seed=1,tol=1e-9,maxiter=500)
    r2=differential_evolution(ear,angles*3+[(0,.006)]*3,seed=1,tol=1e-8,maxiter=800)
    old=(50-b)*A*U*U+b*U*U/2+b*(G(anchor)+slope*(d-anchor))
    print({'U':U,'b':b,'anchor':anchor,'single_loss':r1.fun,'ear_loss_per_edge':r2.fun/2,
           'single_args':r1.x.tolist(),'ear_args':r2.x.tolist(),
           'required_per_edge':(old-math.pi)/(b*U*U)},flush=True)

for b in map(int,sys.argv[2:] or ['15','16','17','18']):
    run(b)
