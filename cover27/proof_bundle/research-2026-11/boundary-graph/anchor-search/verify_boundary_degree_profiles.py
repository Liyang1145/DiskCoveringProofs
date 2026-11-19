"""Combine the earlier exact degree profiles with the boundary apex catalog."""
import argparse
from collections import Counter
import json
from pathlib import Path

from verify_boundary_walk import apex_norm_ceiling, minimum_boundary_neighbors, verify as check_patterns

LEVELS=(812_000_000,833_896_000,876_600_000,892_960_000,901_500_000,905_600_000)


def verify(source):
    data=json.loads(source.read_text(encoding="utf-8"))
    profiles=[tuple(profile) for profile in data["residual"]]
    if data["degreeSum"]!=[50,64] or len(profiles)!=1036 or len(set(profiles))!=1036:
        raise ValueError("incorrect earlier residual catalog")
    for profile in profiles:
        if len(profile)!=14 or not 3<=min(profile)<=max(profile)<=15 or not 50<=sum(profile)<=64:
            raise ValueError("invalid earlier degree profile")
    _,counts=check_patterns()
    result={}
    for lo in LEVELS:
        tally=Counter()
        pairs=0
        for profile in profiles:
            repeats=profile.count(3)
            apices=14-repeats
            if apices not in counts or lo>=apex_norm_ceiling(apices):
                continue
            if sum(profile)-42<minimum_boundary_neighbors(lo):
                continue
            if lo>=901_500_000 and max(profile)>12:
                continue
            tally[apices]+=1
            pairs+=counts[apices]
        result[lo]={"degree_multisets":dict(sorted(tally.items())),
                    "multiset_pattern_pairs":pairs}
        print(f"D1 >= {lo}/1e9: {sum(tally.values())} degree multisets and {pairs} multiset-pattern pairs.")
    return result


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("source",type=Path)
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    report=verify(a.source)
    if a.output:
        a.output.write_text(json.dumps(report,separators=(",",":"))+"\n",encoding="utf-8")
