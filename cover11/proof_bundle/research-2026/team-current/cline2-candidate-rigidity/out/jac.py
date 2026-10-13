import json, io, math
import numpy as np
from mpmath import mp, mpf, sin, cos, acos, sqrt, atan2, diff
mp.dps=40
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
Q=[[int(a) for a in b] for b in D['centers_scaled_1e17']]
S=10**17
cent=[(mpf(x)/S, mpf(y)/S) for x,y in Q]
R0=mpf('0.3799838531198387090485181795734298538115979028573')
rings=[1,3,4,5,6,7,8,9,10]
# angular order
A=sorted([( (atan2(cent[i][1],cent[i][0]) % (2*mp.pi)), i) for i in rings])
order=[i for a,i in A]
print('ring order:',order)
ang0={i:a for a,i in A}
h0,h2=0,2
x0,y0=cent[h0]; x2,y2=cent[h2]
print('hub0',mp.nstr(x0,18),mp.nstr(y0,18),'hub2',mp.nstr(x2,18),mp.nstr(y2,18))

def ringpos(a,t,Rr):
    return (Rr*cos(t),Rr*sin(t)), a

# variables: t0..t8 (angles of ring disks in 'order'), hub0=(u0,v0), hub2=(u2,v2), R
def unpack(z):
    t=[z[k] for k in range(9)]
    hh0=(z[9],z[10]); hh2=(z[11],z[12]); Rr=z[13]
    ringcent={order[k]:t[k] for k in range(9)}
    return ringcent,hh0,hh2,Rr
def pos(ringcent,hh0,hh2,i):
    if i==h0: return hh0
    if i==h2: return hh2
    a=ang0[i]; return (a*cos(ringcent[i]), a*sin(ringcent[i]))

def w_half(s,Rr):
    return acos((1+s*s-Rr*Rr)/(2*s))

# constraints
def F(z):
    rc,hh0,hh2,Rr=unpack(z)
    out=[]
    # spoke constraints: for k, pair (order[k],order[k+1])
    for k in range(9):
        i=order[k]; j=order[(k+1)%9]
        a=ang0[i]; b=ang0[j]
        b=b if b>a else b+2*mp.pi
        out.append(w_half(a,Rr)+w_half(b,Rr)-(b-a))
    # active triples
    triples=[((0,3,5),'rrr'),((0,2,5),'hr'),((0,9,10),'rrh'),((2,5,7),'hr'),
             ((1,2,8),'hr'),((0,2,6),'hr'),((2,6,8),'hr'),((0,4,6),'hr'),((1,2,7),'hr'),
             ((0,9,10),'hh')]
    for tri,kind in triples:
        if kind=='hh':
            A_=pos(rc,hh0,hh2,tri[0]); P=pos(rc,hh0,hh2,1); Qr=pos(rc,hh0,hh2,2)
            mid=((P[0]+Qr[0])/2,(P[1]+Qr[1])/2)
            dx=Qr[0]-P[0]; dy=Qr[1]-P[1]; L=sqrt(dx*dx+dy*dy)/2
            hh=sqrt(Rr*Rr-L*L)
            nx,ny=-dy,dx
            nrm=sqrt(nx*nx+ny*ny)
            V=(mid[0]+hh*nx/nrm, mid[1]+hh*ny/nrm)
            out.append((V[0]-A_[0])**2+(V[1]-A_[1])**2-Rr*Rr)
            out.append((V[0]-P[0])**2+(V[1]-P[1])**2-Rr*Rr)
        else:
            pts=[pos(rc,hh0,hh2,i) for i in tri]
            ax,ay=pts[0]; bx,by=pts[1]; cx,cy=pts[2]
            d=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
            ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
            uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
            V=(ux,uy)
            out.append((V[0]-ax)**2+(V[1]-ay)**2-Rr*Rr)
            out.append((V[0]-bx)**2+(V[1]-by)**2-Rr*Rr)
            out.append((V[0]-cx)**2+(V[1]-cy)**2-Rr*Rr)
    return out

z0=[ang0[i] for i in order]+[x0,y0,x2,y2,R0]
f0=F(z0)
print('residuals at candidate (should be ~0 within rounding):')
mx=0
for k,v in enumerate(f0):
    print('  c%d: %s'%(k,mp.nstr(v,8)))
    mx=max(mx,abs(v))
print('max |residual| =', mp.nstr(mx,6))

# Jacobian
m=len(f0); n=len(z0)
J=np.zeros((m,n))
for j in range(n):
    g=lambda z,j=j: F(z)[0]  # placeholder
for i in range(m):
    for j in range(n):
        def fi(z,i=i): return F(z)[i]
        J[i,j]=float(diff(fi, z0, j))
np.save('out/J.npy',J)
u,s,vt=np.linalg.svd(J)
print()
print('singular values:', ['%.4e'%x for x in s])
print('rows m=%d cols n=%d'%(m,n))
# determine numerical rank
tol=1e-6*s[0]
rk=int((s>tol).sum())
print('rank (tol=1e-6*max) =',rk,'  nullity =',n-rk)
print('smallest 8 sv:',['%.3e'%x for x in s[-8:]])
np.set_printoptions(precision=6,suppress=False)
print()
print('last 3 right singular vectors (candidate null/dof directions):')
for k in range(1,4):
    print(' sv=%.3e'%s[-k], vt[-k])
print()
print('labels: t(5,7,1,8,6,4,9,10,3) u0 v0 u2 v2 R  ==>', order+['u0','v0','u2','v2','R'])
