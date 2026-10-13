"""Independent re-derivation checks for the radius-deficit audit (consistency only)."""
from mpmath import mp, mpf, sin, cos, tan, acot, pi, sqrt, asin, acos
mp.dps=40
U=mpf('0.33173203427623414')

# 1) Voronoi facet geometry: two circles radius Rf,Rg through P,Q; angle at P between them = beta.
#    Set P=(0,0), Q=(l,0) on the x-axis.  Circle through P,Q with radius R has centre (l/2, +-h),
#    h=sqrt(R^2-(l/2)^2).  The angle at P between the two circles:
def beta_of(Rf,Rg,l):
    hf=sqrt(Rf*Rf-(l/2)**2); hg=sqrt(Rg*Rg-(l/2)**2)
    # directions from P: (l/2, hf) and (l/2, -hg)
    v1=(l/2,hf); v2=(l/2,-hg)
    d=(v1[0]*v2[0]+v1[1]*v2[1])/(sqrt(v1[0]**2+v1[1]**2)*sqrt(v2[0]**2+v2[1]**2))
    return acos(d)
for (Rf,Rg,l) in ((U,U,0.5),(U,mpf('0.6')*U,0.5),(mpf('0.8')*U,mpf('0.5')*U,0.3)):
    b=beta_of(Rf,Rg,l)
    # angles at P of the two triangles: gamma = angle between PQ and the radius direction
    gf=asin((l/2)/Rf); gg=asin((l/2)/Rg)
    # exact paired area vs Rf Rg sin beta
    area=mpf(2)*Rf*Rg*sin(b)
    print('Rf=%s Rg=%s l=%s: beta=%s  pi-gf-gg=%s  RfRg sinb=%s'%(mp.nstr(Rf,6),mp.nstr(Rg,6),l,mp.nstr(b,8),mp.nstr(pi-gf-gg,8),mp.nstr(Rf*Rg*sin(b),8)))

# 2) tau identity and deficit chain on a fine legal grid near the boundaries beta->0, beta->pi
print()
bad=[0,0,0]
worst=(mpf('-1e9'),None)
for i in range(1,400):
    beta=pi*mpf(i)/400
    for j in range(1,400):
        gf=pi*mpf(j)/400
        gg=pi-beta-gf
        if gg<=0: continue
        for Rf in (U, mpf('0.9')*U, mpf('0.6')*U, mpf('0.3')*U):
            Rg=Rf*sin(gf)/sin(gg)
            if Rg<=0 or Rg>U: continue
            x,y=Rf/U,Rg/U; tau=abs(x-y)/(x+y); Delta=abs(gf-gg)/2
            if abs(tau-abs(tan(Delta))*tan(beta/2))>1e-15: bad[0]+=1
            if tau*sin(beta) < (1-cos(beta))*Delta-1e-20: bad[1]+=1
            D=U*U*(1-x*y)*sin(beta); rhs=U*U*(1-cos(beta))*Delta
            if D<rhs-1e-20: bad[2]+=1
            v=rhs-D
            if v>worst[0]: worst=(v,(float(beta),float(Delta),float(tau)))
print('grid violations [tau-identity, tau*sinb>=..., D>=rhs]:',bad)
print('worst (rhs - D):',mp.nstr(worst[0],6),'at',worst[1])
