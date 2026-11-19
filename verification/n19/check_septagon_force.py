# SPDX-License-Identifier: MIT
"""Exact stress replay for n19/B12 all-doubleton one-interruption orbits.

Certificate angles and rod weights were proposed numerically, then rounded
to integers. No optimization status or float is used by this verifier.
"""
import argparse
import collections
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations

from compare_census import energy_subgraph, read

D = F(".562071")
PI_LO, PI_HI = F("3.14159265358979"), F("3.14159265358980")
SCALE = 10**10

def check(ok, label):
    if not ok: raise ArithmeticError(label)

def trig(x, sin):
    offset=int(sin)
    terms=[(-1)**k*x**(2*k+offset)/math.factorial(2*k+offset) for k in range(18)]
    mid=sum(terms,F(0))
    n=36+offset
    err=abs(x)**n/math.factorial(n)
    lo=(mid-err)*SCALE
    hi=(mid+err)*SCALE
    return F(lo.numerator//lo.denominator,SCALE),-F((-hi).numerator//(-hi).denominator,SCALE)

def scalar():
    def atan(q, n): return sum(F((-1)**i,(2*i+1)*q**(2*i+1)) for i in range(n))
    MachinLo=16*atan(5,12)-4*atan(239,5)
    MachinHi=16*atan(5,13)-4*atan(239,4)
    check(PI_LO<MachinLo<MachinHi<PI_HI,'Machin bounds')
    check(0<D<1 and trig(D/2,True)[0]>0 and 13*trig(D/2,True)[0]**2>1,'gap cap')
    check(5*D<PI_LO,'short paths monotone')
    return [F(1)]+[trig(k*D,False)[0] for k in range(1,6)]+[F(-1)]

def classify(row):
    masks=row['faces']
    a=[]
    for j in range(12):
        e=(1<<j)|(1<<((j+1)%12))
        v=[(f^e).bit_length()-1 for f in masks if f&e==e]
        check(len(v)==1 and v[0]>=12,'boundary assignment')
        a.extend(v)
    if sorted(collections.Counter(a).values())!=[2]*6: return None
    z=next(i for i in range(12,19) if i not in a)
    cuts=[]
    def has(i,j,k): return ((1<<i)|(1<<j)|(1<<k)) in masks
    for j in range(12):
        x,y=a[j-1],a[j]
        if x!=y and not has(j,x,y):
            check(has(j,x,z) and has(j,y,z),'interrupted assignment')
            cuts.append(j)
    changes=[j for j in range(12) if a[j-1]!=a[j]]
    check(len(changes)==6 and all(j%2==changes[0]%2 for j in changes),'alternating changes')
    check(len(cuts)<=2 and (len(cuts)<2 or (cuts[1]-cuts[0])%12 in (2,10)),'interruptions')
    return len(cuts)

def graph_rod_indices(masks):
    faces=[[i for i in range(19) if f>>i&1] for f in masks]
    check(all(len(f)==3 for f in faces),'face shape')
    return [(i,12+i) for i in range(12)]+[(i,12+(i+1)%12) for i in range(12)]+[(12+i,31+j) for j,face in enumerate(faces) for i in face]

def reduce(graph, weights):
    check(len(graph)==len(weights) and len(set(graph))==len(graph),'rod bundle')
    check(all(w>=0 for w in weights) and sum(weights)>0,'nonnegative weights')
    gn={k:F(w,sum(weights)) for k,w in zip(graph,weights) if w}
    for v in range(54,11,-1):
        links={i:w for (i,j),w in gn.items() if j==v}
        if not links: continue
        sw=sum(links.values())
        for i,j in combinations(sorted(links),2):
            gn[i,j]=gn.get((i,j),F(0))+links[i]*links[j]/sw
        for i in links: del gn[i,v]
    check(all(0<=i<j<12 and c>0 for (i,j),c in gn.items()),'anchor graph')
    return gn

def verify_leaf(masks, th_i, w, cos_lower):
    check(len(th_i)==11 and all(isinstance(t,int) for t in th_i),'theta sample')
    th=[F(0)]+[F(t,10**6) for t in th_i]
    check(all(0<=b-a<=D for a,b in zip(th,th[1:])) and
          0<=2*PI_LO-th[-1]<=2*PI_HI-th[-1]<=D,'base angular domain')
    C=reduce(graph_rod_indices(masks),w)
    E0=F(0); eps=F(0); penalty=F(0)
    g=[F(0)]*12
    for (i,j),c in C.items():
        d=j-i
        h=th[j]-th[i]
        _,cu=trig(h,False)
        sl,su=trig(h,True)
        # E(h)=2c(1-cos h); derivative in h is 2c sin h.
        E0+=2*c*(1-cu)
        g[i]-=c*(sl+su); g[j]+=c*(sl+su)
        # Error for derivative applied to h'-h, whose magnitude is <7.
        eps+=7*c*(su-sl)
        lo=2*PI_LO-(12-d)*D
        hi=d*D
        low=cos_lower[min(d,12-d)]
        if low<0:
            penalty+=c*(-low)*max((lo-h)**2,(hi-h)**2)
    # Linear min over all gaps <=D and fixed sum 2*pi.
    sufs=[sum(g[i+1:]) for i in range(12)]
    linear=D*sum(sufs)-(12*D-2*PI_LO)*max(sufs)-sum(a*b for a,b in zip(g,th))
    return E0+linear-eps-penalty

def examine(census, certificates):
    rows,_=read(Path(census),12,"dfs")
    digest=hashlib.sha256(json.dumps(rows,separators=(",",":")).encode()).hexdigest()
    receipt=json.loads(Path(__file__).with_name("census_receipt.json").read_text())[0]
    check(receipt["owners"]==12 and len(rows)==receipt["orbits"] and
          digest==receipt["orbit_sha256"], "native B12 census binding")
    counts=collections.Counter()
    leaves=set()
    for faces,stabilizer in rows:
        n=classify({"faces":faces})
        if n is None: continue
        counts[n]+=1
        check(energy_subgraph(faces)==(n!=1),"existing energy closure classification")
        if n==1: leaves.add(faces)
    check(counts=={0:11,1:22,2:9},'doubleton family counts')
    certs=json.loads(Path(certificates).read_text())
    check(len(certs)==len(leaves),'candidate certificate count')
    keys={tuple(c['faces']) for c in certs}
    check(keys==leaves,'exact interrupted family binding')
    cl=scalar(); bounds=[]
    for c in certs:
        check(all(type(w)==int for w in c['weights']),'weights integral')
        lower=verify_leaf(c['faces'],c['theta'],c['weights'],cl)
        check(lower>F(1,13),'strict global graph lower bound')
        bounds.append(lower)
    step=10**6
    smallest=min(bounds)
    return {'census_sha256':digest,
            'family_counts':dict(sorted(counts.items())),
            'one_interruption_excluded':len(bounds),
            'uniform_lower_squared_millionths':(smallest*step).numerator//(smallest*step).denominator}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('census',type=Path,help='native dfs-12.json replay output')
    p.add_argument('--certificate',type=Path,default=Path(__file__).with_name('septagon_force.json'))
    a=p.parse_args()
    print(json.dumps(examine(a.census,a.certificate),indent=2))
