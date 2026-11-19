"""Filter the B=14 degree profiles with necessary inner-to-boundary incidences."""
import argparse
from collections import Counter
import json
from pathlib import Path

from verify_boundary_walk import B, apex_norm_ceiling, distance, verify as check_patterns
from verify_ten_boundary_neighbors import LOWER

STEPS=(812_000_000,833_896_000,876_600_000,892_960_000,LOWER,901_500_000)


def count_lower(a):
    return 10 if a>=LOWER else 9 if a>=833_896_000 else 8


def profiles(source):
    old=json.loads(source.read_text(encoding="utf-8"))
    p=[tuple(x) for x in old["residual"]]
    if old["degreeSum"]!=[50,64] or len(p)!=1036 or len(set(p))!=1036:
        raise ValueError("wrong initial boundary degree catalogue")
    if any(len(x)!=B or tuple(sorted(x))!=x or not 3<=min(x)<=max(x)<=15 or not 50<=sum(x)<=64 for x in p):
        raise ValueError("invalid residual profile")
    return p


def apex_neighborhoods(pattern):
    return [set(i for e in block for i in (e,(e+1)%B)) for block in pattern]


def degree_ceiling(neighbors,free):
    """Per-owner cap after counting distinct additional candidate neighbors."""
    mandatory=Counter(i for block in neighbors for i in block)
    high=Counter()
    for ns in neighbors:
        if len(ns)==3:
            continue
        for j in range(B):
            if len(ns)==2 and j not in ns and all(distance(j,i)<=2 for i in ns):
                high[j]+=1
    return sorted(3 if mandatory[i]==1 else 2+mandatory[i]+high[i]+free
                  for i in range(B))


def verify(source):
    old=profiles(source)
    patterns,_=check_patterns()
    by_m={}
    for p in patterns:
        by_m.setdefault(len(p),[]).append(apex_neighborhoods(p))
    report={}
    for a in STEPS:
        q=count_lower(a)
        inner_limit=10 if a>=901_500_000 else 12
        pending=[x for x in old if 14-x.count(3) in by_m
                 and a<apex_norm_ceiling(14-x.count(3)) and sum(x)-42>=q
                 and (a<901_500_000 or max(x)<=12)]
        by_cap={m:Counter(tuple(degree_ceiling(p,inner_limit-m)) for p in record)
                for m,record in by_m.items() if m<=inner_limit}
        pairs=0
        kept=0
        for x in pending:
            m=14-x.count(3)
            total=sum(n for cap,n in by_cap[m].items() if all(d<=c for d,c in zip(x,cap)))
            if total:
                kept+=1
                pairs+=total
        report[a]={"degree_multisets":kept,"multiset_pattern_pairs":pairs}
        print(f"PASS B=14: D1 >= {a}/1e9 leaves {kept} degree multisets and {pairs} multiset-pattern pairs after the incidence bound.")
    return report


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("source",type=Path)
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    result=verify(a.source)
    if a.output:
        a.output.write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8")
