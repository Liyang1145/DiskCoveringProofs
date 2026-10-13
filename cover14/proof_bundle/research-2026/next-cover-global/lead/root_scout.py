"""One bounded numeric root probe; NOT an existence/uniqueness certificate."""
import mpmath as m,json
from pathlib import Path
m.mp.dps=70
ROOT=Path(__file__).resolve().parents[3]
d=json.loads((ROOT/'research-2026/session2/type14/out/hprec_sol.json').read_text())
def geom(z,c,r):
 s=m.sqrt(1-r*r);a=(s+z)/2;t=r+m.sqrt(r*r-z*z)
 b=r+m.sqrt(r*r-(a-z)**2);dd=1-m.sqrt(r*r-c*c)
 return a,b,c,dd,s,z,t,r

def fg(z,c,r):
 a,b,c,dd,s,z,t,r=geom(z,c,r)
 v1=(1+a*a+b*b-r*r)/2;v2=(1+c*c+dd*dd-r*r)/2;det=a*dd-b*c
 F=(v1*dd-v2*b)**2+(a*v2-c*v1)**2-det*det
 # sites (a,b), (c,dd), (0,t); squared area determinant
 cross=(c-a)*(t-b)-(dd-b)*(-a)
 l1=(a-c)**2+(b-dd)**2;l2=c*c+(dd-t)**2;l3=a*a+(b-t)**2
 G=l1*l2*l3-4*r*r*cross*cross
 return F,G

def equations(z,c,r):
 fz,gz=[m.diff(lambda zz:fg(zz,c,r)[i],z) for i in range(2)]
 fc,gc=[m.diff(lambda cc:fg(z,cc,r)[i],c) for i in range(2)]
 return (*fg(z,c,r),fz*gc-fc*gz)

z=m.mpf(d['th'][5]);c=m.mpf(d['th'][2]);r=m.mpf(d['R'])
initial=equations(z,c,r)
sol=m.findroot(equations,(z,c,r),tol=m.mpf('1e-62'),maxsteps=20)
res=equations(*sol)
J=m.matrix([[m.diff(lambda v:equations(*(list(sol)[:j]+[v]+list(sol)[j+1:]))[i],sol[j]) for j in range(3)] for i in range(3)])
out={'status':'numeric_only','scope':'D2 selected radical branches; 3eq stationary root, no global proof','initial_residuals':list(map(str,initial)),'z_c_r':list(map(str,sol)),'a_b_c_d_s_z_t_r':list(map(str,geom(*sol))),'residuals':list(map(str,res)),'Jacobian_determinant':str(m.det(J))}
(Path(__file__).parent/'root-scout.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
