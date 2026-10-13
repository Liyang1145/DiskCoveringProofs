"""Exact subgraph embeddings of the paid 68-rod n21 core into B13 census types.

Records only explicit successful maps, never presumes every near-optimal graph
has this core. Other census types still require strict force/area exclusions.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import time

ROOT=Path(__file__).resolve().parent
N21=ROOT.parent/"n21-global"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as s:
        for block in iter(lambda:s.read(1<<20),b""):
            h.update(block)
    return h.hexdigest()


def verify_mapping(facemasks,mapping,active):
    assert len(mapping)==21 and sorted(mapping)==list(range(21))
    assert sorted(mapping[:13])==list(range(13))
    assert sorted(mapping[13:])==list(range(13,21))
    orientation=next((sgn for sgn in (1,-1)
        if all(mapping[j]==(mapping[0]+sgn*j)%13 for j in range(13))),None)
    assert orientation is not None
    faces=set(facemasks)
    mapped_faces=[sum(1<<mapping[v] for v in f) for f in active]
    assert len(set(mapped_faces))==14 and set(mapped_faces)<=faces
    anchor=[(mapping[0]+orientation*i-(1 if orientation<0 else 0))%13 for i in range(13)]
    # qi lies between ci and ci+1; reflected anchor needs the one-index offset.
    for i in range(13):
        assert {mapping[i],mapping[(i+1)%13]}=={anchor[i],(anchor[i]+1)%13}
    return anchor,mapped_faces


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=ROOT/"evidence/n21-core-embedding-map.json")
    args=parser.parse_args()
    assert not args.output.exists()
    path=ROOT/"evidence/n21-peeling-round5-B13-B14/N21-B13-dfs.json"
    catalog=json.loads(path.read_text())
    assert catalog["complete"] and catalog["N"]==21 and catalog["B"]==13
    assert catalog["screen"] and catalog["orbits"]==583857
    active=json.loads((N21/"evidence/core-system.json").read_text())["active_faces"]
    bb=[]
    for face in active:
        bd=[i for i in face if i<13]
        if len(bd)==2:
            inner=next(i for i in face if i>=13)
            assert (bd[1]-bd[0])%13 in (1,12)
            bb.append((bd,inner))
    assert len(bb)==6 and len({j for _,j in bb})==6
    central=next(j for j in sorted({j for f in active for j in f if j>=13}) if j not in {i for _,i in bb})
    inactive=next(j for j in range(13,21) if j not in {i for f in active for i in f})
    selected=[];start=time.time()
    for index,row in enumerate(catalog["survivors"]):
        masks=row["faces"]
        owners=[-1]*13
        for mask in masks:
            boundary=mask&8191
            if boundary.bit_count()==2 and (mask^boundary).bit_count()==1:
                lo=(boundary&-boundary).bit_length()-1
                hi=(boundary^(1<<lo)).bit_length()-1
                if hi-lo==1:
                    edge=lo
                elif lo==0 and hi==12:
                    edge=12
                else:
                    continue
                owners[edge]=(mask^boundary).bit_length()-1
        found=None
        faces=set(masks)
        for sign in (1,-1):
            if found is not None:
                break
            for shift in range(13):
                mapping=[(shift+sign*j)%13 for j in range(13)]+[-1]*8
                okay=True
                used=set()
                for (a,b),role in bb:
                    x,y=mapping[a],mapping[b]
                    edge=x if (y-x)%13==1 else y
                    owner=owners[edge]
                    if owner<13 or owner in used:
                        okay=False;break
                    used.add(owner);mapping[role]=owner
                if not okay:
                    continue
                extras=[j for j in range(13,21) if j not in used]
                assert len(extras)==2
                for c in extras:
                    mapping[central]=c
                    mapping[inactive]=next(j for j in extras if j!=c)
                    if all(sum(1<<mapping[v] for v in f) in faces for f in active):
                        found=list(mapping)
                        break
                if found is not None:
                    break
        if found is not None:
            anchor,mapped=verify_mapping(masks,found,active)
            selected.append({"index":index,"center_map":found,"anchor_map":anchor,
                             "active_face_masks":mapped})
        if (index+1)%100000==0:
            print("N21 core embeddings scanned",index+1,"explicit successes",len(selected),
                  "seconds",round(time.time()-start,2),flush=True)
    # Replay each emitted witness independently of the proposal search loop.
    for row in selected:
        anchor,mapped=verify_mapping(catalog["survivors"][row["index"]]["faces"],row["center_map"],active)
        assert anchor==row["anchor_map"] and mapped==row["active_face_masks"]
    assert selected
    paid=ROOT/"evidence/n21-positive-core-angle-tree.json.verified.json"
    proof=json.loads(paid.read_text())
    assert proof["verified"] and proof["graph_edges"]==68 and proof["graph_vertices"]==47
    output={"verified":True,"N":21,"B":13,"scanned_complete_catalog":583857,
            "proved_same_core_types":len(selected),"explicit_maps":selected,
            "remaining_B13_types_without_this_core":583857-len(selected),
            "catalog_sha256":sha(path),"core_angle_proof_sha256":sha(paid),
            "source_sha256":sha(Path(__file__)),"seconds":time.time()-start,
            "scope":"explicit positive-core subgraph witnesses only; no inference that all other types are impossible",
            "global_optimality_proved":False}
    args.output.write_text(json.dumps(output,indent=2),encoding="utf8")
    print("N21 exact same-core type linkage PASS:",len(selected),"types; all others remain separate obligations",flush=True)


if __name__=="__main__":
    main()
