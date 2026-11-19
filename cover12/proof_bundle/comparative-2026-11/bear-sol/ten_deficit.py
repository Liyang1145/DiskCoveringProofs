"""Certified arc-deficit inequalities from finite interior witnesses."""

import argparse
from math import isqrt

import numpy as np

from verify_arcs import arc_on_bin, trig_table
from verify_upper import I

K = 10**6
R = 361103
CUT = K-2*R
OUT = K-R
BRAD = 570000
UNIT = 10**6
AHI = 369451
ALO = 369450
PILO = 3141592
TOTAL = 10*AHI-PILO
Q = 10**10


def ceildiv(a,b):
    return -(-a//b)


def radial_table():
    trig = trig_table()
    r = I(R)/K
    from verify_arcs import sincos
    assert (sincos(I(AHI)/UNIT)[0]-r).pos()
    assert (r-sincos(I(ALO)/UNIT)[0]).pos()
    assert (1-r*r-(I(BRAD+R+200)/K)*(I(BRAD+R+200)/K)).pos()
    assert I(PILO).a//UNIT<I("3.1415926").a
    bounds = np.arange(OUT,BRAD+R+200,100,dtype=np.int64)
    loss = []
    for d in bounds:
        d=(int(d)*I.scale)//K
        aq = arc_on_bin(1-r*r,I(1),d,d,trig)
        loss.append(max(0, ALO-ceildiv(aq*UNIT,I.scale)))
    return bounds*bounds,np.array(loss,dtype=np.int64)


def ci(minsum,maxsum, denom):
    return minsum//denom,ceildiv(maxsum,denom)


def Extremes(pts):
    cand = set()
    for j,(x,y) in enumerate(pts):
        x,y=int(x),int(y)
        m = x*x+y*y
        assert m>0
        v = isqrt((R*R*Q*Q)//m)
        a,b=ci(min(x*(Q+v),x*(Q+v+1)),max(x*(Q+v),x*(Q+v+1)),Q)
        c,d=ci(min(y*(Q+v),y*(Q+v+1)),max(y*(Q+v),y*(Q+v+1)),Q)
        cand.add((a,b,c,d))
        for X,Y in pts[:j]:
            X,Y=int(X),int(Y)
            dx,dy=y-Y,X-x
            q=dx*dx+dy*dy
            if 0<q<=4*R*R:
                v = isqrt(((4*R*R-q)*Q*Q)//q)
                for dx0,dy0 in ((dx,dy),(-dx,-dy)):
                    u,z = (x+X)*Q, (y+Y)*Q
                    a,b = ci(u+min(dx0*v,dx0*(v+1)),u+max(dx0*v,dx0*(v+1)),2*Q)
                    c,d = ci(z+min(dy0*v,dy0*(v+1)),z+max(dy0*v,dy0*(v+1)),2*Q)
                    cand.add((a,b,c,d))
    return np.array(sorted(cand),dtype=np.int64).reshape(-1,4)


def assess(pts,rt):
    assert 1<=len(pts)<=1024
    w=pts[:,0]*pts[:,0]+pts[:,1]*pts[:,1]
    assert np.all((0<w)&(w<=BRAD*BRAD))
    cc=Extremes(pts)
    far = np.maximum(abs(cc[:,0]),abs(cc[:,1]))**2+np.maximum(abs(cc[:,2]),abs(cc[:,3]))**2
    z=far>=OUT*OUT
    cc,far=cc[z],far[z]
    levels=np.searchsorted(rt[0],far)
    assert np.all(levels<len(rt[1]))
    x,y=pts[:,0][None,:],pts[:,1][None,:]
    dx=np.maximum(np.maximum(cc[:,0,None]-x,x-cc[:,1,None]),0)
    dy=np.maximum(np.maximum(cc[:,2,None]-y,y-cc[:,3,None]),0)
    inc=(dx*dx+dy*dy<=R*R)
    return inc,rt[1][levels]


def nearest_sq(pts,box):
    x,y=pts[:,0],pts[:,1]
    a,b,c,d=box
    dx=np.maximum(np.maximum(a-x,x-b),0)
    dy=np.maximum(np.maximum(c-y,y-d),0)
    return dx*dx+dy*dy


def shapes(box):
    a,b,c,d,e,f=map(int,box)
    return ((a-f,b-e,c,d),(a+e,b+f,c,d))


def safe(pts,boxes):
    j=np.ones(len(pts),dtype=bool)
    for b in boxes:
        j &= nearest_sq(pts,b)>R*R
    return j


def dirs(n):
    u=np.arange(n)*(2*np.pi/n)
    return np.c_[np.cos(u),np.sin(u)]


def witnesses(box,n,lc):
    centers = shapes(box)
    p=[lc]
    for j,(a,b,c,d) in enumerate(centers):
        xt,yt=(a+b)//2,(c+d)//2
        u=dirs(n)
        w=np.array([max(xt-a,b-xt),max(yt-c,d-yt)])
        rad=R+3+abs(u)@w
        p.append(np.rint(rad[:,None]*u+[xt,yt]).astype(np.int64))
    # Witnesses past intersections of the two inner circles, when possible.
    a,b,c,d,e,f=map(int,box)
    l=max(0,e-(b-a))
    h=isqrt(max(0,R*R-l*l))+3
    p.append(np.array([[(a+b)//2,c-h],[(a+b)//2,d+h]],dtype=np.int64))
    p=np.unique(np.vstack(p),axis=0)
    z=(p*p).sum(axis=1)
    return p[(z<=BRAD*BRAD)&safe(p,centers)]


def weight(pts, rt):
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, hstack
    inc,loss=assess(pts,rt)
    if not len(loss):
        return None
    # Keep only the most stringent row for duplicate incidence patterns.
    by=np.argsort(loss,kind="stable")
    up=np.unique(np.packbits(inc[by],axis=1),return_index=True,axis=0)[1]
    ii=by[up]
    loss=loss[ii]
    inc=inc[ii]
    a=hstack((csr_matrix(inc,dtype=float),csr_matrix(-np.ones((len(ii),1)))))
    fit=linprog(np.r_[-np.ones(len(pts)),10.],A_ub=a,b_ub=loss,
                bounds=(0,None),method="highs")
    if fit.status==3:
        return None
    if not fit.success:
        raise RuntimeError(fit.message)
    ww=np.maximum(np.floor(fit.x[:-1]+1e-9).astype(np.int64),0)
    z=max(0,int(np.ceil(fit.x[-1]+1e-9)),int(np.max(inc@ww-loss)))
    keep=ww>0
    return pts[keep],ww[keep],z,int(ww.sum())-10*z


def verify_weight(pts,ww,z,box,rt):
    assert len(pts)==len(ww) and np.all((0<ww)&(ww<100*UNIT)) and 0<=z<100*UNIT
    assert np.all(safe(pts,shapes(box)))
    inc,loss=assess(pts,rt)
    assert np.all(inc@ww<=loss+z)
    return int(ww.sum())-10*z>TOTAL


def cloud(n=64):
    return np.rint(dirs(n)*(CUT-3)).astype(np.int64)


def trial(x,y,l,eps,n):
    rt=radial_table()
    box=(x-eps,x+eps,y-eps,y+eps,l-eps,l+eps)
    p=witnesses(box,n,cloud())
    if np.any((p*p).sum(axis=1)<CUT*CUT):
        print("central point excludes box",box)
        return True
    if not len(p):
        print("no witness",box)
        return False
    res=weight(p,rt)
    if res is None:
        print("no LP certificate",box)
        return False
    pts,ww,z,v=res
    print("inner box",box,"weight margin",v-TOTAL,"witnesses",len(pts),flush=True)
    if v>TOTAL:
        assert verify_weight(pts,ww,z,box,rt)
        return True
    return False


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("x",type=int,nargs="?",default=0)
    p.add_argument("y",type=int,nargs="?",default=0)
    p.add_argument("l",type=int,nargs="?",default=174000)
    p.add_argument("--eps",type=int,default=0)
    p.add_argument("--n",type=int,default=90)
    a=p.parse_args()
    trial(a.x,a.y,a.l,a.eps,a.n)
