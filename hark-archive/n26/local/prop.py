"""PROPOSAL data (floats -> fixed rationals): u0, tau0=D^+ G u0 on positive rods, v=N u0, a=u0.N.u0."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import numpy as np, json, hp
from fractions import Fraction as F
import os
P=DCP_N26+'/local/prop.json'
if not os.path.exists(P):
    Z=np.load(DCP_N26+'/local/homog2.npz'); G,D,Pr=Z['G'],Z['D'],Z['P']; H0=np.load(DCP_N26+'/local/H0_hp.npy')
    Dp=np.linalg.pinv(D,rcond=1e-10); N=G.T@Dp@G; u0=np.linalg.eigh(H0)[1][:,0]
    if u0[9]<0: u0=-u0
    t=Dp@G@u0; v=N@u0; a=float(u0@v)
    q=lambda x,d=10**12: str(F(int(round(x*d)),d))
    tau=[ '0' ]*134
    for e,x in zip(Pr,t): tau[int(e)]=q(x)
    json.dump({'tau0':tau,'v':[q(x) for x in v],'a':q(a),'mu':'11/200'},open(P,'w'))
J=json.load(open(P)); TAU=[F(x) for x in J['tau0']]; V=[F(x) for x in J['v']]; AA=F(J['a']); MU=F(J['mu'])
def weight(kappa):
    w=[l+kappa*t for l,t in zip(hp.LAM0,TAU)]
    assert all(x>=0 for x in w); return w
def brange(lo,hi):
    c=hp.THSTAR; s1=s2=F(0)
    for vi,a,b,x in zip(V,lo,hi,c):
        p,q=vi*(a-x),vi*(b-x); s1+=min(p,q); s2+=max(p,q)
    return s1,s2
