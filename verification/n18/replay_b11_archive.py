# SPDX-License-Identifier: MIT
"""Replay every eleven-owner orbit against the hash-bound native census."""
import argparse
import gzip
from hashlib import sha256
import json
from pathlib import Path

from force_census import check_chunk_data, load_census, need

HERE=Path(__file__).resolve().parent


def run(census,archive):
    masks=load_census(census)[11]
    raw=archive.read_bytes()
    payload=json.loads(gzip.decompress(raw))
    need(payload["schema"]=="n18-force-chunk-archive-v1" and payload["owners"]==11,
         "archived family/schema mismatch")
    size=payload["chunk_size"]
    need(size==12 and len(masks)==397,"unexpected B11 family size")
    starts=list(range(0,len(masks),size))
    chunks=payload["chunks"]
    need(len(chunks)==len(starts),"missing or extra B11 chunk")
    nodes=0
    for start,chunk in zip(starts,chunks,strict=True):
        need(not check_chunk_data(chunk,11,start,masks[start:start+size],{},True),
             "unresolved B11 row")
        nodes+=sum(sum(row["replay"].values()) for row in chunk["records"])
    return dict(status="entire_b11_family_excluded_not_global_proof",
                owners=11,replayed=len(masks),unresolved=0,proof_nodes=nodes,
                archive_sha256=sha256(raw).hexdigest())


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("census",type=Path)
    p.add_argument("--archive",type=Path,default=HERE/"force_b11.json.gz")
    a=p.parse_args()
    print(json.dumps(run(a.census,a.archive),indent=2))
