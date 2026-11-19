# SPDX-License-Identifier: MIT
"""Check two n16 native Voronoi peeling census outputs."""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, permutations
import json
from pathlib import Path

SCALE=100000
CAPS=(9974,21143,37566)
TRIAL=F("0.308220")
CANDIDATE=[
    (0,1,12),(0,11,12),(1,2,12),(2,3,13),(2,12,13),(3,4,13),
    (4,5,13),(5,6,14),(5,13,14),(6,7,14),(7,8,14),(8,9,15),
    (8,14,15),(9,10,15),(10,11,15),(11,12,15),(12,13,15),(13,14,15),
]


def check(condition, message):
    if not condition:
        raise ValueError(message)


def check_caps():
    # Machin's formula: six terms are a lower bound on arctan(1/5),
    # while one term is an upper bound on arctan(1/239).
    pi_lo=16*sum((F((-1)**i,(2*i+1)*5**(2*i+1)) for i in range(6)),F(0))-F(4,239)
    def sin_lo(x):
        check(0<x<F(6,5),"Taylor argument")
        return x-x**3/6+x**5/120-x**7/5040+x**9/362880-x**11/39916800
    for j,a in enumerate(CAPS,1):
        check(sin_lo(pi_lo*a/SCALE)>j*TRIAL,f"cap {j}")
    check(sin_lo(pi_lo/10)>TRIAL and (TRIAL/(1-2*TRIAL))**2<F(3,4),"boundary count")


def read(path,b,mode):
    d=json.loads(path.read_bytes())
    expected=dict(complete=True,N=16,B=b,scale=SCALE,screen=True,caps=list(CAPS),mode=mode)
    check(all(d.get(k)==v for k,v in expected.items()),"run metadata")
    rows=[]
    ring={tuple(sorted((i,(i+1)%b))) for i in range(b)}
    for row in d["survivors"]:
        masks=tuple(row["faces"])
        s=row["stabilizer"]
        check(len(masks)==30-b and masks==tuple(sorted(set(masks))),"face count or order")
        check(all(0<m<2**16 and m.bit_count()==3 for m in masks),"invalid face")
        check(s>=1 and 2*b%s==0,"invalid stabilizer")
        edges=Counter()
        for m in masks:
            vs=[i for i in range(16) if m>>i&1]
            edges.update(combinations(vs,2))
        check(ring<=edges.keys() and all(v==(1 if k in ring else 2)
                                       for k,v in edges.items()),"edge incidence")
        check({i for edge in edges for i in edge}==set(range(16)),"missing vertex")
        rows.append((masks,s))
    check(len(set(rows))==len(rows)==d["orbits"],"orbit count")
    check(sum(2*b//s for _,s in rows)==d["rooted"],"rooted count")
    return sorted(rows),d["calls"]


def candidate_labels():
    keys=set()
    for start in range(12):
        for direction in (-1,1):
            for perm in permutations(range(12,16)):
                label=[(start+direction*i)%12 for i in range(12)]+list(perm)
                keys.add(tuple(sorted(sum(1<<label[i] for i in f) for f in CANDIDATE)))
    return keys


def verify(directory):
    check_caps()
    keys=candidate_labels()
    results=[]
    for b in (11,12):
        rows,dfs=read(directory/f"dfs-{b}.json",b,"dfs")
        audits,audit=read(directory/f"audit-{b}.json",b,"audit")
        check(rows==audits,f"censuses disagree for b={b}")
        match=[s for f,s in rows if b==12 and f in keys]
        check(len(match)==int(b==12),"missing or duplicate candidate topology")
        results.append(dict(owners=b,orbits=len(rows),dfs_calls=dfs,audit_calls=audit,
                            orbit_sha256=sha256(json.dumps(rows,separators=(",",":")).encode()).hexdigest(),
                            attaining_candidate_topology_stabilizers=match))
    return results


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory",type=Path)
    print(json.dumps(verify(parser.parse_args().directory),indent=2))
