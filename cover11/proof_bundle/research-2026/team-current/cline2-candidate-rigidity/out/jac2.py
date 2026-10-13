import json, io, math
import numpy as np
from mpmath import mp, mpf, sin, cos, acos, sqrt, atan2
mp.dps=50
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
S=10**17
cent=[(mpf(int(x))/S, mpf(int(y))/S) for x,y in D['centers_scaled_1e17']]
R0=mpf('0.3799838531198387090485181795734298538115979028573')
rings=[1,3,4,5,6,7,8,9,10]
h0,h2=0,2
A=sorted([(atan2(cent[i][1],cent[i][0])%(2*mp.pi), i) for i in rings])
order=[i for a,i in A]; ang0={i:a for a,i in A}
edges=[(0,3,5),(0,2,5),(0,9,10),(2,5,7),(1,2,8),(0,2,6),(2,6,8),(0,4,6),(1,2,7),(0,9,10)]
VARL=order+['u0','v0','u2','v2','R']
def unpackp(t,u0,v0,u2,v2,Rr):
    rc=dict(zip(order,t))
    def pos(i):
        if i==h0: return (u0,v0)
        if i==h2: return (u2,v2)
        a=ang0[i]; return (a*cos(rc[i]), a*sin(rc[i]))
    return pos,Rr
def cen3(P,Q,Rp):
    ax,ay=P; bx,by=Q; cx,cy=Rp
    d=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
    uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
    return (ux,uy)
def cons(t,u0,v0,u2,v2,Rr):
    pos,R=unpackp(t,u0,v0,u2,v2,Rr); out=[]
    for k in range(9):
        i=order[k]; j=order[(k+1)%9]
        a=ang0[i]; b=ang0[j]; 
        if b<a: b=b+2*mp.pi
        out.append(acos((1+a*a-R*R)/(2*a))+acos((1+b*b-R*R)/(2*b))-(b-a))
    for tri in edges:
        if tri==(0,9,10):
            P=pos(h0); Q=pos(h2); Wp=pos(0)
            mx=(P[0]+Q[0])/2; my=(P[1]+Q[1])/2
            dx=(Q[0]-P[0])/2; dy=(Q[1]-P[1])/2
            L=sqrt(dx*dx+dy*dy); hh=sqrt(R*R-L*L)
            nx,ny=-dy,dx
            for s in (mpf(1),mpf(-1)):
                V=(mx+s*hh*nx, my+s*hh*ny)
                e=[(V[0]-P[0])**2+(V[1]-P[1])**2-R*R,(V[0]-Wp[0])**2+(V[1]-Wp[1])**2-R*R]
                if max(abs(e[0]),abs(e[1]))<mpf('1e-12'): out+=e
        else:
            P,Q,Rp=[pos(i) for i in tri]
            V=cen3(P,Q,Rp)
            out+=[(V[0]-P[0])**2+(V[1]-P[1])**2-R*R,(V[0]-Q[0])**2+(V[1]-Q[1])**2-R*R,(V[0]-Rp[0])**2+(V[1]-Rp[1])**2-R*R]
    return out
z=[ang0[i] for i in order]+[cent[0][0],cent[0][1],cent[2][0],cent[2][1],R0]
f0=cons(z[0:9],z[9],z[10],z[11],z[12],z[13])
print('num constraints',len(f0))
print('max |residual| =',mp.nstr(max(abs(v) for v in f0),8))
for k,v in enumerate(f0): print('  c%02d %s'%(k,mp.nstr(v,6)))
# numeric jacobian via central differences
n=len(z); m=len(f0); h=mpf('1e-20')
J=np.zeros((m,n))
for j in range(n):
    zp=list(z); zm=list(z)
    zp[j]=zp[j]+h; zm[j]=zm[j]-h
    fp=cons(zp[0:9],zp[9],zp[10],zp[11],zp[12],zp[13]); fm=cons(zm[0:9],zm[9],zm[10],zm[11],zm[12],zm[13])
    for i in range(m): J[i,j]=float((fp[i]-fm[i])/(2*h))
np.save('out/J_tight.npy',J)
u,s,vt=np.linalg.svd(J)
print()
print('m=%d n=%d'%(m,n))
print('singular values:'); print(['%.4e'%x for x in s])
rk=int((s>1e-5*s[0]).sum()); print('rank=%.0f  nullity=%d'%(rk,n-rk))
print()
print('variables:',VARL)
for k in range(1,min(n-rk,4)+1):
    print('null vec (sv=%.2e):'%s[-k], np.round(vt[-k],6))
