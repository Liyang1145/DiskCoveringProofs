"""Pair every annulus with every core fill and apply rational area bounds."""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

from verify_boundary_walk import B
from verify_b14_core_marks import K


def degrees(faces):
    vertices=set(i for f in faces for i in f)
    result={v:0 for v in vertices}
    edges={tuple(sorted(e)) for f in faces for e in combinations(f,2)}
    for i,j in edges:
        result[i]+=1
        result[j]+=1
    return result


def core_profile(ds):
    return (tuple(sorted(ds[i] for i in range(K))),
            tuple(sorted(ds[i] for i in range(K,K+3))))


def write_groups(path,fills):
    core=json.loads(fills.read_text(encoding="utf-8"))["triangulations"]
    groups=Counter(core_profile(degrees(faces)) for faces in core)
    rows=[[a,b,groups[a,b]] for a,b in sorted(groups)]
    path.write_text(json.dumps(rows,separators=(",",":"))+"\n",encoding="utf-8")


def verify(annuli,fills,supports,core_area=None,angular=None):
    ring=json.loads(annuli.read_text(encoding="utf-8"))
    core=json.loads(fills.read_text(encoding="utf-8"))["triangulations"]
    area=json.loads(supports.read_text(encoding="utf-8"))
    outer={tuple(map(int,d.split(","))):int(v) for d,v in area["supports"]}
    inner={k:int(v) for k,v in enumerate(area["enclosed"]) if v is not None}
    annulus_types=[]
    for i in ring["orbit_representative_indices"]:
        record=ring["strips"][i]
        cap=outer[tuple(sorted(record["outer_degrees"]))]
        ds=degrees(record["triangles"])
        if any(ds[j]!=degree for j,degree in enumerate(record["outer_degrees"])):
            raise ValueError("annulus degree calculation")
        # Subtract the two cycle edges that would be counted in both graphs.
        extra=tuple(ds[j]-2 for j in record["inner_cycle"])
        if len(extra)!=K or sum(extra)!=B+K:
            raise ValueError("unexpected number of links across the annulus")
        annulus_types.append((cap,extra))
    core_types=Counter()
    core_groups=Counter()
    for faces in core:
        ds=degrees(faces)
        if len(ds)!=K+3 or sum(ds.values())!=52:
            raise ValueError("wrong core degree total")
        profile=core_profile(ds)
        core_groups[profile]+=1
        core_types[tuple(ds[i] for i in range(K)),profile]+=1
    groups=list(sorted(core_groups))
    area_records=[] if core_area is None else json.loads(core_area.read_text(encoding="utf-8"))
    schedules={}
    for rec in area_records:
        flags=rec["group_excluded"]
        if len(flags)!=len(groups) or any(not isinstance(x,bool) for x in flags):
            raise ValueError("core area groups have incompatible classes")
        failed={g for g,f in zip(groups,flags) if f}
        if sum(core_groups[g] for g in failed)!=rec["excluded_core_fills"]:
            raise ValueError("mismatched core area exclusion count")
        schedules[rec["owner_norm_floor"]]=failed
    for floor in sorted(schedules):
        schedules[floor]=set.union(*(s for a,s in schedules.items() if a<=floor))
    results=Counter()
    retained={a:0 for a in schedules}
    exclusions={}
    if angular is not None:
        if set(angular)!=set(schedules) or any(len(v)!=len(annulus_types) for v in angular.values()):
            raise ValueError("angular exclusions do not match the annulus catalogue")
        exclusions={floor:tuple(all(angular[a][i]>0 for a in angular if a<=floor)
                                for i in range(len(annulus_types))) for floor in angular}
    surviving_angles={a:0 for a in exclusions}
    entries=[(cost,profile,sum(inner[d] for d in profile[1]),n)
             for (cost,profile),n in core_types.items()]
    for index,(cap,extra) in enumerate(annulus_types):
        excluded=0
        live=Counter()
        for cost,profile,inside,multiplicity in entries:
            if cap+inside+sum(inner[d+e] for d,e in zip(cost,extra))<0:
                excluded+=multiplicity
            else:
                live[profile]+=multiplicity
        results[excluded]+=1
        for floor,failed in schedules.items():
            available=sum(n for profile,n in live.items() if profile not in failed)
            retained[floor]+=available
            if floor in exclusions and exclusions[floor][index]:
                surviving_angles[floor]+=available
    count=len(annulus_types)*len(core)
    removed=sum(k*v for k,v in results.items())
    print(f"PASS B=14: {removed} of {count} annulus and core-fill pairs fail the Voronoi degree-area bound.")
    print(f"{len(annulus_types)-results[0]} annuli lose at least one completion; {results[len(core)]} annuli lose all completions.")
    for floor,n in sorted(retained.items()):
        print(f"PASS B=14: at D1 >= {floor}/1e6, at most {n} pairs remain after both area bounds.")
    for floor,n in sorted(surviving_angles.items()):
        print(f"PASS B=14: at D1 >= {floor}/1e6, at most {n} pairs remain after area and angular tests.")
    return {"annuli":len(annulus_types),"core_fills":len(core),"excluded_pairs":removed,
            "retained_pairs":count-removed,"combined_retained_pairs":retained,
            "angular_retained_pairs":surviving_angles,
            "histogram":sorted(results.items())}


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("annuli",type=Path)
    p.add_argument("fills",type=Path)
    p.add_argument("supports",type=Path)
    p.add_argument("--core-area",type=Path)
    p.add_argument("--annulus-angles",type=Path)
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    angular=None
    if a.annulus_angles is not None:
        records=json.loads(a.annulus_angles.read_text(encoding="utf-8"))
        angular={row["owner_norm_floor"]//1000:row["placements_per_annulus"] for row in records}
    result=verify(a.annuli,a.fills,a.supports,a.core_area,angular)
    if a.output:
        a.output.write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8")
