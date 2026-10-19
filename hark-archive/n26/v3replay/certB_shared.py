"""Checker B for shared annulus LOCAL-SLAB files (lleaves/shared/*.json): every piece re-checked by local/certB.check_leaf
(mpmath iv 420-bit Kron/Schur energy, Fraction PSD, breakpoint LP) on the FILE's whole box; b-range re-derived from raw
prop.json V and kkt2 c*; contiguity + coverage. Result keyed by file sha256 in verB_shared.json.
A node box contained in a file box inherits the bound (statement is for all theta in the file box with b in [ba,bb]).
usage: certB_shared.py <budget_s>"""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import sys,os,json,time,hashlib,glob
from fractions import Fraction as F
sys.path.insert(0,DCP_N26+'/local')
import certB as LB
ROOT=DCP_N26; D=ROOT+'/v3replay/lleaves/shared'; ST=ROOT+'/v3replay/verB_shared.json'
PJ=json.load(open(ROOT+'/local/prop.json')); V=[F(x) for x in PJ['v']]
S=json.load(open(ST)) if os.path.exists(ST) else {}
T0=time.time(); BUD=float(sys.argv[1]); n=0
def save(): json.dump(S,open(ST+'.tmp','w')); os.replace(ST+'.tmp',ST)
files=sorted(glob.glob(D+'/m*_s*.json'))
for p in files:
    raw=open(p,'rb').read(); h=hashlib.sha256(raw).hexdigest(); key=os.path.basename(p)
    if key in S and S[key]['sha256']==h: continue
    if time.time()-T0>BUD: break
    d=json.loads(raw); lo=[F(x) for x in d['lower']]; hi=[F(x) for x in d['upper']]; mu=F(d['mu']); assert mu>=0
    b1=sum(min(v*(a-c),v*(b-c)) for v,a,b,c in zip(V,lo,hi,LB.CS)); b2=sum(max(v*(a-c),v*(b-c)) for v,a,b,c in zip(V,lo,hi,LB.CS))
    ps=d['pieces']; assert d['closed'] and F(ps[0]['ba'])<=b1 and F(ps[-1]['bb'])>=b2, key
    for x,y in zip(ps,ps[1:]): assert x['bb']==y['ba'], key
    worst=None
    for x in ps:
        kap=F(x['kappa']); w=[a+kap*t for a,t in zip(LB.L0,LB.TAU)]; assert all(y>=0 for y in w)
        bd=LB.check_leaf(w,lo,hi,F(x['ba']),F(x['bb']),mu); assert bd is not None and bd>0,(key,x['ba'])
        worst=bd if worst is None else min(worst,bd)
    S[key]={'sha256':h,'ok':True,'lower':d['lower'],'upper':d['upper'],'b_cov':[ps[0]['ba'],ps[-1]['bb']],'min_bound':str(worst)}
    n+=1
    if n%10==0: save()
save()
print(json.dumps({'checked_now':n,'have':len(S),'files':len(files)}))
