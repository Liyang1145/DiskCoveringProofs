"""Content-bound union of root and refinement proposal receipts.

Only organizes untrusted receipts. The standalone checker must replay all
exclusions before a mathematical aggregate conclusion can be accepted.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
ROOT=Path(__file__).resolve().parent

if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def sha(path):
    h=hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda:stream.read(1<<20),b""):
            h.update(block)
    return h.hexdigest()


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--groups",type=Path,required=True)
    parser.add_argument("--root",type=Path,required=True)
    parser.add_argument("--trees",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    assert not args.output.exists()
    data=json.loads(args.groups.read_text());hashed=sha(args.groups)
    root=json.loads(args.root.read_text());trees=json.loads(args.trees.read_text())
    assert root["groups_sha256"]==trees["groups_sha256"]==hashed
    assert root["B"]==trees["B"]==data["B"] and data["N"]==21
    old={r["group"]:r for r in root["outcomes"]}
    new={r["group"]:r for r in trees["outcomes"]}
    assert len(old)==len(root["outcomes"]) and set(old)==set(range(data["group_count"]))
    assert len(new)==len(trees["outcomes"])
    assert set(new)=={j for j,r in old.items() if r["status"]=="pending"}
    merged=[]
    for j in range(data["group_count"]):
        record=dict(new[j] if j in new else old[j])
        if record["status"]=="excluded":
            folder=args.trees.parent if j in new else args.root.parent
            target=folder/f"group-{j:07}.json.gz"
            assert sha(target)==record["tree_sha256"]
            record["certificate_path"]=target.resolve().relative_to(ROOT.resolve()).as_posix()
        merged.append(record)
    membership=Counter(b["group"] for b in data["bindings"])
    assert sum(membership.values())==data["scanned_types"]
    covered=sum(membership[j] for j,r in enumerate(merged) if r["status"]=="excluded")
    result={"N":21,"B":data["B"],"groups_sha256":hashed,"outcomes":merged,
            "excluded_group_count":sum(r["status"]=="excluded" for r in merged),
            "pending_group_count":sum(r["status"]=="pending" for r in merged),
            "catalog_member_exclusions":covered,"pending_catalog_members":data["scanned_types"]-covered,
            "root_receipt_sha256":sha(args.root),"tree_receipt_sha256":sha(args.trees),
            "mathematical_exclusions_freshly_replayed":False,
            "global_optimality_proved":False,"source_sha256":sha(Path(__file__))}
    args.output.write_text(json.dumps(result,indent=2),encoding="utf8")
    print("Combined B",data["B"],"receipts:",covered,"selected types excluded;",
          result["pending_catalog_members"],"selected types still pending",flush=True)


if __name__=="__main__":
    main()
