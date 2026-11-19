# SPDX-License-Identifier: MIT
"""Verify the native n19 census interface and count the energy-covered subgraphs."""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path


def caps():
    # Machin and alternating Taylor bounds; all trig inputs are below 1.
    arctan5 = sum(F((-1)**i, (2*i+1)*5**(2*i+1)) for i in range(6))
    pi_lo = 16*arctan5-F(4,239)
    for n,c in enumerate((8946,18717,31284), 1):
        x=pi_lo*c/100000
        s=x-x**3/6+x**5/120-x**7/5040
        if not 0<x<1 or not s>0 or not 13*s*s>n*n:
            raise ArithmeticError(f"angular cap {n} not certified")


def energy_subgraph(faces):
    # For each outer site, accumulate the allowed paired inner spokes.
    edge_sets=[set() for _ in range(12)]
    for face in faces:
        v=[i for i in range(19) if face & (1<<i)]
        if len(v)!=3:
            raise ArithmeticError("face mask not a triple")
        if v[0]<12<=v[1]:
            edge_sets[v[0]].add((v[1],v[2]))

    def cyclic_pairs(i, pairs, vertices):
        if i==6:
            return tuple(sorted((vertices[-1],vertices[0]))) in pairs[5]
        for a,b in pairs[i-1]:
            if b==vertices[-1]:
                a,b=b,a
            if a==vertices[-1] and b not in vertices:
                if cyclic_pairs(i+1,pairs,vertices+(b,)):
                    return True
        return False

    # All boundary cycle rotations/reflections reduce to picking parity
    # and the direction of the ordered initial core pair.
    for parity in (0,1):
        pairs=edge_sets[parity::2]
        for a,b in pairs[0]:
            if cyclic_pairs(2,pairs,(a,b)) or cyclic_pairs(2,pairs,(b,a)):
                return True
    return False


def read(path, b, mode):
    data=json.loads(path.read_bytes())
    required=dict(complete=True,N=19,B=b,scale=100000,screen=True,
                  caps=[8946,18717,31284],mode=mode)
    if any(data[k]!=v for k,v in required.items()):
        raise ArithmeticError(f"incorrect run metadata: {path.name}")
    rows=[(tuple(row["faces"]), row["stabilizer"]) for row in data["survivors"]]
    if len(rows)!=len(set(rows)) or len(rows)!=data["orbits"]:
        raise ArithmeticError("missing or duplicate orbit")
    if any(len(fs)!=36-b or list(fs)!=sorted(set(fs)) or
           any(x.bit_count()!=3 or x>=2**19 for x in fs) or
           s<1 or 2*b%s for fs,s in rows):
        raise ArithmeticError("invalid face list or stabilizer")
    if sum(2*b//s for _,s in rows)!=data["rooted"]:
        raise ArithmeticError("inconsistent orbit/stabilizer accounting")
    return sorted(rows), data["calls"]


def verify(directory):
    caps()
    results=[]
    for b in (12,13,14):
        rows,dfs=read(directory/f"dfs-{b}.json",b,"dfs")
        audit_rows,audit=read(directory/f"audit-{b}.json",b,"audit")
        if rows!=audit_rows:
            raise ArithmeticError(f"traversals disagree for b={b}")
        result={"owners":b,"orbits":len(rows),"dfs_calls":dfs,"audit_calls":audit,
                "orbit_sha256":hashlib.sha256(json.dumps(rows,separators=(",",":")).encode()).hexdigest()}
        if b==12:
            result["energy_subgraph_orbits"]=sum(energy_subgraph(f) for f,_ in rows)
        results.append(result)
    return results


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory",type=Path)
    print(json.dumps(verify(parser.parse_args().directory),indent=2))
