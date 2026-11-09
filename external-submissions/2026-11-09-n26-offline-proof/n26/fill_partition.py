"""Check or extend an exact angular partition for one remaining filling."""

import argparse
import json
from collections import Counter
from pathlib import Path

from verify_belt_geometry import graph_from_faces
from verify_candidate_cell import replay_partition
from verify_fan import require
from verify_outer_windows import model_windows
from verify_patch14 import RADIUS
from verify_shell_fills import origin_cap, parse_fill
from verify_shells import angles, parse_shell
from verify_template import certified_trial_radius


def native(node):
    if "exclusion" in node:
        return node["exclusion"]
    require("split" in node, "Cannot export an incomplete partition")
    return {"split":node["split"],"lower":native(node["lower"]),"upper":native(node["upper"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shells",type=Path)
    parser.add_argument("fill",type=Path,help="TSV containing exactly one filling")
    parser.add_argument("windows",type=Path)
    parser.add_argument("--disks",type=int,required=True)
    parser.add_argument("--boundary",type=int,required=True)
    parser.add_argument("--core",action="store_true",help="Partition separately for each possible origin disk")
    parser.add_argument("--tight-radius",action="store_true")
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--nodes",type=int,default=0,help="New nodes per origin branch, zero for replay")
    parser.add_argument("--tighten",action="store_true")
    parser.add_argument("--relative",action="store_true")
    parser.add_argument("--export",type=Path,help="Write a fill certificate if every node is closed")
    args = parser.parse_args()
    n,b = args.disks,args.boundary
    line, = args.fill.read_text(encoding="utf-8").splitlines()
    i,inner = parse_fill(line,n,b)
    shells = args.shells.read_text(encoding="utf-8").splitlines()
    require(0 <= i < len(shells), "Unknown shell")
    h,outer,_ = parse_shell(shells[i],n,b)
    faces = outer+inner
    require(len(faces) == 2*n-b-2, "Wrong triangle count")
    windows = model_windows(args.windows,n,b)
    edges = angles(b,n,faces,windows)
    trial = certified_trial_radius() if args.tight_radius else RADIUS
    require(trial <= RADIUS, "The trial exceeds the angular bound radius")
    cap = min(origin_cap(n,b,h,windows),trial) if args.core else None
    origins = list(range(b+h,n)) if args.core else [None]
    require(origins, "Missing possible origin disks")
    header = {"index":i,"shell":shells[i],"fill":line,"disks":n,"boundary":b,
              "tight":args.tight_radius,"core":args.core}
    record = {"model":header,"parts":[{"open":True} for _ in origins]}
    if args.out.exists():
        record = json.loads(args.out.read_text(encoding="utf-8"))
        require(record["model"] == header and len(record["parts"]) == len(origins),
                "Partition checkpoint belongs to a different filling")
    for u,part in zip(origins,record["parts"]):
        graph = graph_from_faces(n,faces,u,b)
        if args.nodes:
            from find_candidate_partition import save, search_domains
            search_domains(part,graph,edges,trial,args.nodes,lambda:save(record,args.out),
                           boundary=b,cap=cap,tighten_bounds=args.tighten,refine=True,reuse=True,
                           relative=args.relative,use_mean=True)
            save(record,args.out)
    counts = Counter()
    for u,part in zip(origins,record["parts"]):
        graph = graph_from_faces(n,faces,u,b)
        counts.update(replay_partition(part,graph,edges,trial,boundary=b,cap=cap))
    print(f"PASS b={b}, shell={i}, excluded={counts['excluded']}, open={counts['open']}",flush=True)
    if args.export is not None and not counts["open"]:
        proof = {"fill":line,"full_angles":True,"tight":args.tight_radius}
        if args.core:
            proof["trees"] = [native(part) for part in record["parts"]]
        else:
            proof["tree"] = native(record["parts"][0])
        out = {"index":i,"shell":shells[i],"proofs":[proof]}
        args.export.write_text(json.dumps(out,separators=(",",":"))+"\n",encoding="utf-8")


if __name__ == "__main__":
    main()
