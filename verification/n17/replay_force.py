#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Replay all available n=17 noncandidate force certificates against the native census."""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[1]/"tools"))
from check_native_n17_census import EXPECTED, verify_record
from force_prototype import need, verify_tree


def check(directory, certs, complete):
    censuses={b:json.loads((directory/f"n17-B{b}.json").read_text()) for b in EXPECTED}
    for b,d in censuses.items():
        verify_record(d,b,"dfs")
    required={(b,i) for b,d in censuses.items() for i in range(len(d["survivors"]))}
    required.remove((12,629))
    seen={}
    for path in certs:
        for row in json.loads(path.read_text()):
            b,i=row["owners"],row["index"]
            need((b,i) in required and (b,i) not in seen,"duplicate or invalid certificate")
            need(row["faces"]==censuses[b]["survivors"][i]["faces"],"wrong census graph")
            seen[b,i]=verify_tree(b,row["faces"],row["tree"])
    open_by_family={b:[i for j,i in sorted(required-seen.keys()) if j==b] for b in EXPECTED}
    totals={k:sum(d[k] for d in seen.values()) for k in ("force","split","empty")}
    print(json.dumps({"certified":len(seen),"requested":len(required),
                      "unresolved":open_by_family,"leaves_and_splits":totals},indent=2))
    need(not complete or set(seen)==required,"noncandidate replay incomplete")
    return seen


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("directory",type=Path)
    p.add_argument("certificates",nargs="+",type=Path)
    p.add_argument("--require-complete",action="store_true")
    a=p.parse_args()
    check(a.directory,a.certificates,a.require_complete)
