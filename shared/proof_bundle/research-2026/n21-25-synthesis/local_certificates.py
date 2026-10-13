"""Exact active-core anchor isolation for n22..24, no complete angular-domain claim."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from math import isqrt
import argparse
import hashlib
import json

ROOT=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--n",type=int,nargs="+",default=[22,23,24])
    args=parser.parse_args()
    for n in args.n:
        folder=ROOT/f"evidence/n{n}"
        d=json.loads((folder/"core-system.json").read_text())
        root=json.loads((folder/"core-root.json").read_text())
        accepted=json.loads((folder/"algebraic-check1/root-verified.json").read_text())
        assert accepted["verified"] and accepted["root_sha256"]==hashlib.sha256((folder/"core-root.json").read_bytes()).hexdigest()
        gamma,lam,nu,radius=((500,F(1,2000),F(1,100),F(3,50)) if n in (22,23)
                            else (300,F(1,5000),F(1,100),F(1,20)))
        g,b=d["G"],d["B"];edges=d["edges"];m=len(edges)
        q=10**15
        x=[F(int(v),int(root["Qx"])) for v in root["xnum"]]
        a=[]
        for v in x:
            z=v*q;a.append((2*z.numerator+z.denominator)//(2*z.denominator))
        rho,eps,buffer=F(1,10**80),F(2,q),F(1,10**8)
        assert all(abs(F(a[j],q)-x[j])+rho<=eps for j in list(range(g))+list(range(g+1,len(x))))
        assert all(0<v-rho<v+rho<F(1,10) for v in x[g+1:g+1+m])
        assert all(-nu<v-rho<v+rho<0 for v in x[g+1+m:])
        points=[[q,0]]+[a[2*j:2*j+2] for j in range(g//2)]
        jac,weights=[],[]
        lap=[[0]*g for _ in range(g)];degree=Counter()
        for k,(u,v) in enumerate(edges):
            degree.update((u,v));row=[0]*g
            for axis in (0,1):
                for node,sign in ((u,1),(v,-1)):
                    if node:
                        j=2*(node-1)+axis
                        row[j]+=2*sign*(points[u][axis]-points[v][axis])
                        for other,osign in ((u,1),(v,-1)):
                            if other:
                                lap[j][2*(other-1)+axis]+=a[g+1+k]*sign*osign
            jac.append(row);weights.append(a[g+1+k]**2)
        nq=nu*q;assert nq.denominator==1
        for node in range(1,b):
            row=[0]*g
            for axis in (0,1):
                j=2*(node-1)+axis;row[j]=2*points[node][axis]
                lap[j][j]+=a[g+1+m+node-1]
            jac.append(row);weights.append(nq.numerator**2)
        assert sum(v*v for row in jac for v in row)<144*q*q
        assert max(weights)*100<q*q
        # Every rod row has at most four entries, each perturbing by <=4 eps.
        structural_entries=4*m+2*(b-1)
        da=4*(isqrt(structural_entries)+1)*eps
        error=(2*max(degree.values())+1)*eps+gamma*(F(1,100)*(24+da)*da+eps/4*(12+da)**2)
        assert error<buffer
        den=q**4
        h=[[lap[i][j]*q**3+gamma*sum(weights[k]*jac[k][i]*jac[k][j] for k in range(len(jac)))
            for j in range(g)] for i in range(g)]
        for i in range(g):
            diff=(buffer+(lam if i<2*(b-1) else 0))*den
            assert diff.denominator==1;h[i][i]-=diff.numerator
        previous,hashes=1,[]
        for k in range(g):
            pivot=h[k][k]
            assert pivot>0,("not positive definite",n,k)
            hashes.append(hashlib.sha256(pivot.to_bytes((pivot.bit_length()+7)//8,"big")).hexdigest())
            for i in range(k+1,g):
                for j in range(i,g):
                    value,rem=divmod(pivot*h[i][j]-h[i][k]*h[k][j],previous)
                    assert not rem;h[i][j]=h[j][i]=value
            previous=pivot
        gap=lam-2*gamma*nu**2*radius**2
        assert gap>0
        result={"verified":True,"N":n,"scope":"active-core anchor isolation only; not all topologies or all angles",
                "geometry_dimension":g,"positive_leading_principal_minors":g,
                "gamma":gamma,"lambda":str(lam),"nu":str(nu),"anchor_radius":str(radius),
                "isolation_margin":str(gap),"matrix_perturbation_bound":str(error),
                "principal_minor_binary_sha256":hashes,
                "root_sha256":hashlib.sha256((folder/"core-root.json").read_bytes()).hexdigest(),
                "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                "global_optimality_proved":False}
        target=folder/"local-isolation-certificate.json"
        assert not target.exists()
        target.write_text(json.dumps(result,indent=2),encoding="utf8")
        print("N",n,"EXACT",g,"D ANCHOR ISOLATION PASS; radius",radius,"gap",gap,flush=True)


if __name__=="__main__":
    main()
