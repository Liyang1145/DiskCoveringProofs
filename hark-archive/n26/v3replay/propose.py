import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_MAIN_REPO
import sys,json,math
from fractions import Fraction as F
import numpy as np, cvxpy as cp, mpmath as mp
sys.path.insert(0,DCP_MAIN_REPO+'/cover26/proof_bundle/outputs/n26-sharp-candidate-angles-published-replay-v1')
from n26_force import load_trig, rod_graph, spanning_tree
from n26_direct_arc_force import force_check
mp.mp.dps=40
RUP=F("0.234700090400448239616790133776692127560495963654971391785925")
P=json.load(open(DCP_MAIN_REPO+'/cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json'))
spec=P['spec'];arcs=load_trig()[0]
NV,E=rod_graph(spec); b=spec['B']
parent,order,chords=spanning_tree(NV,E)
Inc=np.zeros((NV,len(E)))
for k,(u,v) in enumerate(E): Inc[u,k]+=1; Inc[v,k]-=1
def propose(lo,hi,solver='CLARABEL'):
    G=cp.Variable((b-1,2)); Fl=cp.Variable((len(E),2))
    pm=[];dp=[];H=[]
    for l,h in zip(lo,hi):
        m=mp.mpf(l.numerator)/l.denominator/2+mp.mpf(h.numerator)/h.denominator/2
        pm.append([float(mp.cos(2*mp.pi*m)),float(mp.sin(2*mp.pi*m))]); dp.append([-pm[-1][1],pm[-1][0]])
        H.append(float(mp.pi*(mp.mpf(h.numerator)/h.denominator-mp.mpf(l.numerator)/l.denominator)))
    pm=np.array(pm);dp=np.array(dp);H=np.array(H)
    load=cp.vstack([ -cp.sum(G,axis=0,keepdims=True), G, np.zeros((NV-b,2))]) if False else None
    cons=[Inc[0]@Fl==-cp.sum(G,axis=0)]
    cons+=[Inc[1:b]@Fl==G, Inc[b:]@Fl==0]
    cons+=[cp.sum(cp.norm(Fl,2,axis=1))<=1]
    obj=cp.sum(cp.multiply(G,pm-np.array([1.0,0.0])))-cp.sum(cp.multiply(H,cp.abs(cp.sum(cp.multiply(G,dp),axis=1))))-cp.sum(cp.multiply(H**2/2,cp.norm(G,2,axis=1)))
    pr=cp.Problem(cp.Maximize(obj),cons)
    pr.solve(solver=solver,tol_gap_abs=1e-13,tol_gap_rel=1e-13,tol_feas=1e-13,max_iter=500) if solver=='CLARABEL' else pr.solve(solver=solver)
    return pr.value, G.value, Fl.value
def rationalize(lo,hi,Gv,Fv,qs=(10**12,10**15,10**18,10**21)):
    best=None
    for q in qs:
        cert={'q':q,'g':[int(round(x*q)) for x in Gv.reshape(-1)],
              'f':[int(round(Fv[k][d]*q)) for k in chords for d in range(2)]}
        r=force_check(spec,lo,hi,cert,arcs); m=F(r['required_radius_lower'])-RUP
        if best is None or m>best[1]: best=(cert,m)
    return best
if __name__=='__main__':
    B=json.load(open('boxes.json'))['boxes']
    for t in sys.argv[1:]:
        lo=[F(x) for x in B[t]['lo']];hi=[F(x) for x in B[t]['hi']]
        v,Gv,Fv=propose(lo,hi)
        c,m=rationalize(lo,hi,Gv,Fv)
        print(t,'float',v-float(RUP),'exact',float(m),flush=True)
