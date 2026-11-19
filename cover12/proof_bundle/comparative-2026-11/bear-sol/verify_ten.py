"""Replay a proof that ten outer and two inner disks cannot cover at R."""

import argparse
import gzip
import json
import time
from pathlib import Path

import numpy as np

from ten_deficit import (
    BRAD, CUT, K, OUT, R, TOTAL, cloud, radial_table, safe, shapes,
    verify_weight, weight, witnesses,
)

ROOT = (0,OUT,0,OUT,0,OUT)
CERT = Path("ten_certificate.jsonl.gz")


def box_len(box):
    return tuple(box[i+1]-box[i] for i in (0,2,4))


def half(box,axis):
    j=2*axis
    a,b=box[j:j+2]
    assert a+1<b
    m=(a+b)//2
    return box[:j]+(a,m)+box[j+2:],box[:j]+(m,b)+box[j+2:]


def geometric(box):
    a,b,c,d,e,f=box
    # The right center must remain inside the non-boundary radius; the
    # left center is no farther from O than the right.
    if (a+e)**2+c*c>OUT*OUT:
        return True
    s=minabs(a-f,b-e)**2+c*c
    if s>R*R:
        return True
    # If the inner disks do not overlap, one must contain the central disk.
    return e>R and s>(R-CUT)**2


def minabs(a,b):
    return max(a,-b,0)


def central_ok(pt,box):
    x,y=pt
    return x*x+y*y<CUT*CUT and bool(safe(np.array([pt],dtype=np.int64),shapes(box))[0])


def replay(f,root=ROOT):
    rt=radial_table()
    todo=[root]
    stats={"s":0,"g":0,"c":0,"w":0}
    margin = 10**12
    with gzip.open(f,"rt",encoding="ascii") as inp:
        for physical in inp:
            row=json.loads(physical)
            assert todo
            box=todo.pop()
            method=row[0]
            stats[method]+=1
            if method=="s":
                assert len(row)==2 and type(row[1]) is int and 0<=row[1]<3
                u,v=half(box,row[1])
                todo.extend((v,u))
            elif method=="g":
                assert len(row)==1 and geometric(box)
            elif method=="c":
                assert len(row)==3 and all(type(i) is int and abs(i)<=K for i in row[1:])
                assert central_ok(row[1:],box)
            elif method=="w":
                z,triples=row[1:]
                assert type(z) is int and 0<=z<100*K
                assert 1<=len(triples)<=384 and all(len(p)==3 for p in triples)
                assert all(type(x) is int and abs(x)<=BRAD and type(y) is int and abs(y)<=BRAD
                           and type(w) is int and 0<w<100*K for x,y,w in triples)
                p=np.array(triples,dtype=np.int64)
                assert verify_weight(p[:,:2],p[:,2],z,box,rt)
                margin=min(margin,int(p[:,2].sum())-10*z-TOTAL)
            else:
                raise ValueError("unknown certificate node")
        assert not todo
    print("PASS: ten-outer parameter tree",stats,"minimum weight margin",margin,flush=True)


def generate(f,root=ROOT):
    rt=radial_table()
    lc=cloud(192)
    todo=[root]
    visits=passes=splits=0
    start=time.monotonic()
    with gzip.open(f,"xt",encoding="ascii",compresslevel=3) as fp:
        while todo:
            box=todo.pop()
            visits+=1
            lens=box_len(box)
            if visits%100==0:
                print("tree",visits,"leaves",passes,"splits",splits,"remaining",len(todo),
                      "elapsed",round(time.monotonic()-start,1),"box",box,flush=True)
            row=None
            if geometric(box):
                row=["g"]
            else:
                ss=safe(lc,shapes(box))
                if np.any(ss):
                    row=["c",*map(int,lc[np.flatnonzero(ss)[0]])]
                elif max(lens)<=75000:
                    ns = (56,) if max(lens)>16000 else ((76,) if max(lens)>6000 else (100,160))
                    for n in ns:
                        p=witnesses(box,n,lc[:0])
                        if not len(p):
                            continue
                        z=(p*p).sum(axis=1)
                        if np.any(z<CUT*CUT):
                            row=["c",*map(int,p[np.flatnonzero(z<CUT*CUT)[0]])]
                            break
                        res=weight(p,rt)
                        if res is None:
                            continue
                        w,ww,off,val=res
                        if val>TOTAL:
                            assert verify_weight(w,ww,off,box,rt)
                            row=["w",off,np.c_[w,ww].tolist()]
                            break
            if row is None:
                j=max(range(3),key=lambda j:lens[j])
                if lens[j]<=1600:
                    raise RuntimeError(f"unclosed box {box} after {visits} visits")
                u,v=half(box,j)
                row=["s",j]
                todo.extend((v,u))
                splits+=1
            else:
                passes+=1
            fp.write(json.dumps(row,separators=(",",":"))+"\n")
    print("Generated complete certificate:",f,visits,"nodes and",passes,"leaves",flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--generate",action="store_true")
    p.add_argument("--file",type=Path,default=CERT)
    p.add_argument("--root",type=int,nargs=6,default=ROOT)
    a=p.parse_args()
    (generate if a.generate else replay)(a.file,tuple(a.root))
