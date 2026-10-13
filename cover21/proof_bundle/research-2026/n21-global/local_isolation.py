"""Exact n21 active-core anchor isolation. Does not isolate the movable slack center."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import hashlib
import json
import time

ROOT = Path(__file__).resolve().parent
EV = ROOT/"evidence"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def main():
    start = time.time()
    data = json.loads((EV/"core-system.json").read_text())
    root = json.loads((EV/"core-root.json").read_text())
    verified = json.loads((EV/"core-root-verified.json").read_text())
    assert verified["verified"] and verified["root_sha256"] == hashlib.sha256((EV/"core-root.json").read_bytes()).hexdigest()
    g,b = data["G"],data["B"]
    edges = data["edges"]
    m = len(edges)
    q = 10**15
    eps,buffer,rho = F(2,q),F(1,10**8),F(1,10**80)
    gamma,lam,nu,radius = 200,F(1,2000),F(1,100),F(1,10)
    x = [F(int(v),int(root["Qx"])) for v in root["xnum"]]
    rounded = []
    for value in x:
        v = value*q
        rounded.append((2*v.numerator+v.denominator)//(2*v.denominator))
    relevant = list(range(g))+list(range(g+1,len(x)))
    assert all(abs(F(rounded[j],q)-x[j])+rho <= eps for j in relevant)
    assert all(0 < v-rho < v+rho < F(1,10) for v in x[g+1:g+1+m])
    assert all(-nu < v-rho < v+rho < 0 for v in x[g+1+m:])
    points = [[q,0]]+[rounded[2*j:2*j+2] for j in range(g//2)]
    a,weights = [],[]
    lap = [[0]*g for _ in range(g)]
    degrees = Counter()
    for k,(u,v) in enumerate(edges):
        degrees.update((u,v))
        row = [0]*g
        for d in (0,1):
            for node,sign in ((u,1),(v,-1)):
                if node:
                    j = 2*(node-1)+d
                    row[j] += 2*sign*(points[u][d]-points[v][d])
                    for other,osign in ((u,1),(v,-1)):
                        if other:
                            lap[j][2*(other-1)+d] += rounded[g+1+k]*sign*osign
        a.append(row)
        weights.append(rounded[g+1+k]**2)
    nuq = nu*q
    assert nuq.denominator == 1
    for node in range(1,b):
        row = [0]*g
        for d in (0,1):
            j = 2*(node-1)+d
            row[j] = 2*points[node][d]
            lap[j][j] += rounded[g+1+m+node-1]
        a.append(row)
        weights.append(nuq.numerator**2)
    assert len(a) == 80 and g == 92 and m == 68
    assert sum(v*v for row in a for v in row) < 100*q*q
    assert 100*max(weights) < q*q
    # At most 4 eps entry error, 80*92<10000; 400 eps Frobenius bound is safe.
    da = 400*eps
    error = (2*max(degrees.values())+1)*eps + gamma*(F(1,100)*(20+da)*da+eps/4*(10+da)**2)
    assert error < buffer
    den = q**4
    h = [[lap[i][j]*q**3+gamma*sum(weights[k]*a[k][i]*a[k][j] for k in range(len(a)))
          for j in range(g)] for i in range(g)]
    for i in range(g):
        subtract = (buffer+(lam if i < 2*(b-1) else 0))*den
        assert subtract.denominator == 1
        h[i][i] -= subtract.numerator
    previous,hashes = 1,[]
    for k in range(g):
        pivot = h[k][k]
        assert pivot > 0, ("positive definiteness failed",k)
        hashes.append(hashlib.sha256(pivot.to_bytes((pivot.bit_length()+7)//8,"big")).hexdigest())
        for i in range(k+1,g):
            for j in range(i,g):
                value,remainder = divmod(pivot*h[i][j]-h[i][k]*h[k][j],previous)
                assert remainder == 0
                h[i][j] = h[j][i] = value
        previous = pivot
    gap = lam-2*gamma*nu**2*radius**2
    assert gap == F(1,10000) > 0
    result = {"verified":True,"scope":"92-coordinate positive-weight core only; free slack center not isolated",
              "gamma":gamma,"lambda":str(lam),"nu":str(nu),"anchor_radius":str(radius),
              "positive_leading_principal_minors":g,"principal_minor_binary_sha256":hashes,
              "matrix_perturbation_bound":str(error),"isolation_margin":str(gap),
              "root_sha256":hashlib.sha256((EV/"core-root.json").read_bytes()).hexdigest(),
              "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "global_optimality_proved":False,"seconds":time.time()-start}
    certificate = {k:v for k,v in result.items() if k != "seconds"}
    immutable = EV/"local-isolation-certificate.json"
    canonical = json.dumps(certificate,indent=2)
    if immutable.exists():
        assert immutable.read_text(encoding="utf8") == canonical, "Mathematical local certificate changed"
    else:
        immutable.write_text(canonical,encoding="utf8")
    result["mathematical_certificate_sha256"] = hashlib.sha256(immutable.read_bytes()).hexdigest()
    (EV/"local-isolation-verified.json").write_text(json.dumps(result,indent=2),encoding="utf8")
    print("N21 EXACT CORE ANCHOR ISOLATION: radius 1/10, 92 positive principal minors, margin 1/10000",flush=True)


if __name__ == "__main__":
    main()
