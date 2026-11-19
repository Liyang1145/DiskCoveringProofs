# SPDX-License-Identifier: MIT
"""Check strict angular caps and cross-compare fresh n18 peeling censuses."""
import argparse
from collections import defaultdict, deque
from fractions import Fraction as Q
import hashlib
from itertools import combinations
import json
from math import factorial
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from diskcover_n18_algebraic import FACES

N = 18
SCALE = 10**5
CAPS = (9372, 19708, 33621)
U = Q(290167718, 10**9)
ORIGIN = "7063d6fbd45786696873b13c5d8b07e657bcdf47c685b0aae8392876373e53d0"


def need(ok, text):
    if not ok:
        raise ArithmeticError(text)


def caps():
    # Machin: lower for the positive term, upper for the negative term.
    a = lambda q,n: sum(Q((-1)**i,(2*i+1)*q**(2*i+1)) for i in range(n))
    p = 16*a(5,12)-4*a(239,11)
    s = lambda x: sum((-1)**i*x**(2*i+1)/factorial(2*i+1) for i in range(8))
    # The alleged candidate is checked by the separate root checker.
    need(U < Q(291,1000), "owner peeling cutoff")
    need(s(p/10)>U, "B<=10 not excluded")
    need((1-2*U)**2>2*U**2, "B>=14 not excluded")
    for k,c in enumerate(CAPS,1):
        x=p*c/SCALE
        need(0<x< Q(11,10) and 2*c<SCALE and s(x)>k*U, f"cap {k} invalid")


def load(path,b,mode):
    data=json.loads(path.read_bytes())
    metadata=dict(complete=True,N=N,B=b,scale=SCALE,screen=True,caps=list(CAPS),mode=mode)
    need(all(data.get(k)==v for k,v in metadata.items()), f"run metadata mismatch {path}")
    rows=[]
    for rec in data["survivors"]:
        fs,s=tuple(rec["faces"]),rec["stabilizer"]
        need(len(fs)==34-b and tuple(sorted(set(fs)))==fs and
             all(type(m) is int and 0<m<2**N and m.bit_count()==3 for m in fs),
             "invalid canonical face list")
        need(type(s) is int and 1<=s<=2*b and (2*b)%s==0, "invalid stabilizer")
        rows.append((fs,s))
    need(len(rows)==len(set(fs for fs,_ in rows))==data["orbits"],"orbit count/uniqueness")
    need(sum(2*b//s for _,s in rows)==data["rooted"],"rooted/stabilizer accounting")
    return sorted(rows),data["calls"]


def candidate_code():
    b=12
    edge=defaultdict(set)
    for face in FACES:
        for u,v in combinations(face,2):
            edge[frozenset((u,v))].add(face)
    forms=[]
    for direction in (-1,1):
        for start in range(b):
            label={(start+direction*i)%b:i for i in range(b)}
            a,v=start,(start+direction)%b
            f,=edge[frozenset((a,v))]
            seen={f}
            queue=deque([(f,a,v)])
            row=[]
            while queue:
                f,u,v=queue.popleft()
                w,=set(f)-{u,v}
                if w not in label:
                    label[w]=len(label)
                row.append(sum(1<<label[z] for z in f))
                for i,j in ((v,w),(w,u)):
                    for ff in edge[frozenset((i,j))]-seen:
                        seen.add(ff)
                        queue.append((ff,i,j))
            need(len(seen)==len(FACES) and len(label)==N, "candidate traversal disconnected")
            forms.append(tuple(sorted(row)))
    best=min(forms)
    return best,forms.count(best)


def verify(directory):
    caps()
    result=[]
    for b in (11,12,13):
        dfs,d=load(directory/f"dfs-{b}.json",b,"dfs")
        audit,a=load(directory/f"audit-{b}.json",b,"audit")
        need(dfs==audit,f"canonical survivors differ at B={b}")
        row=dict(owners=b,orbits=len(dfs),dfs_calls=d,audit_calls=a,
                 orbit_sha256=hashlib.sha256(json.dumps(dfs,separators=(",",":")).encode()).hexdigest())
        if b==12:
            cand=candidate_code()
            need(cand in dfs,"certified upper candidate missing from census")
            row["candidate_stabilizer"]=cand[1]
            row["candidate_orbit_sha256"]=hashlib.sha256(json.dumps(cand[0],separators=(",",":")).encode()).hexdigest()
        result.append(row)
    return dict(status="topological_necessary_conditions_not_global_lower_bound",
                origin_sha256=ORIGIN,radius_cap=str(U),angle_cap_scale=SCALE,
                angle_cap_numerators=list(CAPS),results=result)


if __name__=="__main__":
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument("directory",type=Path)
    print(json.dumps(verify(a.parse_args().directory),indent=2))
