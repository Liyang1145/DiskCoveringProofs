"""Exact boundary-exposed-face group codec. Proposals alone are not proof of exclusion.

Every returned map explicitly embeds the canonical partial faces in the full
input graph, including the reflected one-index anchor correction.
"""
from pathlib import Path
from itertools import permutations,product
from collections import defaultdict,Counter
import argparse
import hashlib
import json
import time

ROOT=Path(__file__).resolve().parent
PARENT=ROOT.parent
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as s:
        for v in iter(lambda:s.read(1<<20),b""):
            h.update(v)
    return h.hexdigest()


def bits(mask):
    out=[]
    while mask:
        low=mask&-mask;out.append(low.bit_length()-1);mask-=low
    return tuple(out)


def canonical_partial(B,fullmasks,minimum_boundary=1):
    assert 12<=B<=14 and len(fullmasks)==40-B
    bdmask=(1<<B)-1
    assert minimum_boundary in (0,1,2)
    partial=[bits(m) for m in fullmasks if (m&bdmask).bit_count()>=minimum_boundary]
    used=sorted({j for f in partial for j in f if j>=B})
    adjacency=[set() for _ in range(21)]
    for fa in partial:
        for j in fa:
            adjacency[j].update(v for v in fa if v!=j)
    # Degree profile pruning is exact: all roots with min invariant retained.
    profile=None;roots=[]
    for sign in (1,-1):
        for shift in range(B):
            order=[(shift+sign*j)%B for j in range(B)]
            p=tuple(len(adjacency[j]) for j in order)
            if profile is None or p<profile:
                profile=p;roots=[]
            if p==profile:
                roots.append((shift,sign))
    best=None;bestmap=None;tested=0
    for shift,sign in roots:
        inverse={((shift+sign*j)%B):j for j in range(B)}
        colors=defaultdict(list)
        for j in used:
            mask=sum(1<<inverse[v] for v in adjacency[j] if v<B)
            colors[(len(adjacency[j]),mask)].append(j)
        blocks=[colors[key] for key in sorted(colors)]
        for choices in product(*(permutations(block) for block in blocks)):
            interior=[j for block in choices for j in block]
            old_to_new=dict(inverse)
            old_to_new.update({v:B+k for k,v in enumerate(interior)})
            code=tuple(sorted(sum(1<<old_to_new[v] for v in f) for f in partial))
            tested+=1
            if best is None or code<best:
                best=code
                # Canonical center index -> original full center index.
                center=[(shift+sign*j)%B for j in range(B)]+interior
                anchor=[(shift+sign*j-(1 if sign<0 else 0))%B for j in range(B)]
                bestmap={"centers":center,"anchors":anchor,"orientation":sign,"shift":shift}
    assert best is not None
    validate_embedding(B,best,bestmap,fullmasks)
    return best,bestmap,{"retained_faces":len(best),"retained_centers":B+len(used),
                        "deleted_internal_faces":len(fullmasks)-len(best),
                        "normalizing_maps_tested":tested}


def validate_embedding(B,code,mapping,fullmasks):
    center=mapping["centers"];anchors=mapping["anchors"]
    assert len(center)>=B and len(set(center))==len(center)
    assert sorted(center[:B])==list(range(B)) and all(B<=j<21 for j in center[B:])
    assert sorted(anchors)==list(range(B))
    full=set(fullmasks)
    for mask in code:
        vertices=bits(mask)
        assert len(vertices)==3 and all(v<len(center) for v in vertices)
        assert sum(1<<center[v] for v in vertices) in full
    for i in range(B):
        assert {center[i],center[(i+1)%B]}=={anchors[i],(anchors[i]+1)%B}


def transforms(B,masks,shift,sign,interior):
    mapping=[(shift+sign*j)%B for j in range(B)]+interior
    return sorted(sum(1<<mapping[v] for v in bits(mask)) for mask in masks)


def tests(B,rows,minimum_boundary=1):
    import random
    rng=random.Random(20261004+B)
    for row in rows:
        masks=row["faces"]
        code,mapping,info=canonical_partial(B,masks,minimum_boundary)
        for _ in range(3):
            shift=rng.randrange(B);sign=rng.choice((1,-1))
            inner=list(range(B,21));rng.shuffle(inner)
            image=transforms(B,masks,shift,sign,inner)
            other,mp,_=canonical_partial(B,image,minimum_boundary)
            assert other==code
            validate_embedding(B,other,mp,image)
    return {"verified":True,"rows":len(rows),"random_relabel_controls":3*len(rows)}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--B",type=int,choices=(13,14),required=True)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--samples",type=int,default=100)
    parser.add_argument("--full",action="store_true")
    parser.add_argument("--minimum-boundary-vertices",type=int,choices=(0,1,2),default=1)
    parser.add_argument("--parent-groups",type=Path)
    parser.add_argument("--parent-proof",type=Path)
    parser.add_argument("--omit-paid-core-types",action="store_true")
    args=parser.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    B=args.B
    path=PARENT/f"evidence/n21-peeling-round5-B13-B14/N21-B{B}-dfs.json"
    data=json.loads(path.read_text())
    assert data["complete"] and data["N"]==21 and data["B"]==B and data["screen"]
    rows=data["survivors"];n=len(rows)
    selected=None
    selection={}
    if args.parent_groups is not None:
        assert args.parent_proof is not None
        parent=json.loads(args.parent_groups.read_text())
        proof=json.loads(args.parent_proof.read_text())
        assert parent["B"]==B and parent.get("all_selected_types_scanned",parent["full_catalog_scanned"])
        assert parent["catalog_sha256"]==sha(path)
        assert proof["groups_sha256"]==sha(args.parent_groups)
        paid={row["group"] for row in proof["outcomes"] if row["status"]=="excluded"}
        covered={row["group"] for row in proof["outcomes"]}
        assert covered==set(range(parent["group_count"]))
        selected=[bind["index"] for bind in parent["bindings"] if bind["group"] not in paid]
        assert len(set(selected))==len(selected)
        selected.sort()
        selection={"parent_groups_sha256":sha(args.parent_groups),"parent_proof_sha256":sha(args.parent_proof),
                   "parent_selected_types":len(parent["bindings"]),
                   "omitted_parent_excluded_types":len(parent["bindings"])-len(selected),
                   "scope":"selection trusts no theorem; final aggregation must replay all omitted parent certificates"}
    if args.omit_paid_core_types:
        assert B==13
        core_path=PARENT/"evidence/n21-core-embedding-map.json"
        core=json.loads(core_path.read_text())
        assert core["verified"] and core["catalog_sha256"]==sha(path)
        coreindices={row["index"] for row in core["explicit_maps"]}
        assert len(coreindices)==30
        if selected is None:
            selected=list(range(n))
        before=len(selected)
        selected=[i for i in selected if i not in coreindices]
        selection.update(core_map_sha256=sha(core_path),omitted_paid_core_types=before-len(selected))
    controls=tests(B,[rows[i*n//min(20,n)] for i in range(min(20,n))],args.minimum_boundary_vertices)
    eligible=list(range(n)) if selected is None else selected
    count=len(eligible) if args.full else min(len(eligible),args.samples)
    indices=eligible if args.full else sorted({eligible[i*len(eligible)//count] for i in range(count)})
    groups={};bindings=[];start=time.time();statistics=Counter()
    for index in indices:
        code,mapping,info=canonical_partial(B,rows[index]["faces"],args.minimum_boundary_vertices)
        group=groups.setdefault(code,len(groups))
        bindings.append({"index":index,"group":group,"map":mapping})
        statistics[(info["retained_centers"],info["retained_faces"])]+=1
        if len(bindings)%50000==0:
            print("Boundary groups B",B,"scanned",len(bindings),"groups",len(groups),
                  "seconds",round(time.time()-start,2),flush=True)
    ordered=[None]*len(groups)
    for code,index in groups.items():
        ordered[index]={"id":index,"faces":list(code),"centers":max(v for m in code for v in bits(m))+1}
    if args.full and args.minimum_boundary_vertices==0:
        assert len(ordered)==len(bindings),"Complete catalogue contains duplicate full triangulation orbits"
    result={"verified_embeddings":True,"B":B,"N":21,"full_catalog_scanned":args.full and selected is None,
            "all_selected_types_scanned":args.full,"selection":selection,
            "minimum_boundary_vertices_in_retained_faces":args.minimum_boundary_vertices,
            "catalog_types":n,"scanned_types":len(bindings),"group_count":len(groups),
            "groups":ordered,"bindings":bindings,"controls":controls,
            "signature_count_by_vertices_faces":[{"centers":a,"faces":b,"types":k} for (a,b),k in sorted(statistics.items())],
            "catalog_sha256":sha(path),"source_sha256":sha(Path(__file__)),
            "global_optimality_proved":False,"exclusions_proved":False,"seconds":time.time()-start}
    (args.output/"GROUPS.json").write_text(json.dumps(result,separators=(",",":")),encoding="utf8")
    print("B",B,"boundary-exposed grouping",len(bindings),"types ->",len(groups),"groups",flush=True)


if __name__=="__main__":
    main()
