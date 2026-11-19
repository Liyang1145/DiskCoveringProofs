# SPDX-License-Identifier: MIT
"""After the native scan is idle, replay numeric hints for unresolved rows.

Builds exact, standalone original-label witnesses in place; keeps all old
native decisions and replaces a pending row only after exact replay.
"""
import argparse
import json
from pathlib import Path
from force_census import check_chunk_data, load_census, need, write_json
from noncandidate_data_replay import replay


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("census",type=Path)
    p.add_argument("chunks",type=Path)
    p.add_argument("root",type=Path)
    p.add_argument("forest",type=Path)
    p.add_argument("--owners",nargs="+",type=int,choices=[11,12,13],default=[12,13])
    p.add_argument("--max",type=int,dest="limit")
    a=p.parse_args()
    rows=load_census(a.census)
    todo={}
    for b in a.owners:
        for path in sorted(a.chunks.glob(f"{b}-*.json")):
            chunk=json.loads(path.read_bytes())
            start,stop=chunk["start"],chunk["stop"]
            need(0<=start<stop<=len(rows[b]),"chunk index outside census")
            for i,rec in enumerate(chunk["records"],start):
                need(tuple(rec["faces"])==rows[b][i] and rec["index"]==i,"chunk orbit mismatch")
                if rec["status"]=="unresolved":
                    need((b,i) not in todo,"duplicate orbit")
                    todo[b,i]=path
    pairs=list(todo)[:a.limit]
    if not pairs:
        print("no unresolved rows")
        return
    out=replay(a.root,a.census,a.forest,pairs,True)
    for alt in out["rows"]:
        b,i=alt["owners"],alt["index"]
        path=todo[b,i]
        chunk=json.loads(path.read_bytes())
        k=i-chunk["start"]
        prev=chunk["records"][k]
        need(prev["status"]=="unresolved" and tuple(prev["faces"])==alt["native_faces"],
             "concurrent writer or unexpected prior orbit")
        chunk["records"][k]={"index":i,"faces":alt["native_faces"],
          "status":"excluded_force_original_labels",
          "source_faces":alt["source_faces"],"witness_nodes":alt["witness_nodes"],
          "replay":{"nodes":alt["nodes"],"count":alt["count"]}}
        write_json(path,chunk)
    print(f"recorded {len(out['rows'])} standalone original-label witnesses")


if __name__=="__main__":
    main()
