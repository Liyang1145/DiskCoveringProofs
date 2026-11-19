# SPDX-License-Identifier: MIT
"""Build or replay a deterministic gzip of n18's exact force chunks."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import gzip
from hashlib import sha256
import json
from pathlib import Path

from force_census import check_chunk_data, load_census, need, special, write_json

SCHEMA="n18-force-all-families-v1"
B=(11,12,13)
CHUNK=12


def pack(directory,archive):
    chunks=[]
    for b,count in ((11,397),(12,6971),(13,7191)):
        for start in range(0,count,CHUNK):
            stop=min(count,start+CHUNK)
            path=directory/f"{b}-{start:05}-{stop:05}.json"
            need(path.is_file(),f"missing input chunk {path.name}")
            data=json.loads(path.read_bytes())
            need((data["owners"],data["start"],data["stop"])==(b,start,stop),
                 "input chunk order mismatch")
            need(all(row["status"] in ("excluded_force","excluded_force_original_labels","verified_candidate_orbit")
                     for row in data["records"]),"cannot package unresolved chunk")
            chunks.append(data)
    payload=dict(schema=SCHEMA,owners=list(B),chunk_size=CHUNK,chunks=chunks)
    raw=(json.dumps(payload,separators=(",",":"))+"\n").encode()
    import tempfile
    with tempfile.NamedTemporaryFile(dir=archive.parent,prefix=archive.name+".",
                                     suffix=".pending",delete=False) as file:
        file.write(gzip.compress(raw,mtime=0))
        pending=Path(file.name)
    pending.replace(archive)


def replay_archive_chunk(job):
    b,start,masks,closed,chunk=job
    need(not check_chunk_data(chunk,b,start,masks,closed,True),"unresolved proof row")
    nodes=0
    candidates=0
    origins=Counter()
    for entry in chunk["records"]:
        if entry["status"]=="verified_candidate_orbit":
            candidates+=1
        else:
            origins[entry["status"]]+=1
            record=entry["replay"]
            nodes+=record["nodes"] if "nodes" in record else sum(record.values())
    return b,nodes,candidates,origins


def replay(census,root,tree,archive,workers=1):
    need(type(workers) is int and 1<=workers<=6,"invalid archive replay worker count")
    rows=load_census(census)
    closed=special(census,rows,root,tree)
    raw=archive.read_bytes()
    payload=json.loads(gzip.decompress(raw))
    need(payload["schema"]==SCHEMA and payload["owners"]==list(B)
         and payload["chunk_size"]==CHUNK,"incorrect archive metadata")

    jobs=[(b,start,masks[start:start+CHUNK]) for b,masks in rows.items()
          for start in range(0,len(masks),CHUNK)]
    chunks=payload["chunks"]
    need(len(chunks)==len(jobs),"missing or extra archive chunks")
    work=((b,start,masks,closed[b],chunk)
          for (b,start,masks),chunk in zip(jobs,chunks,strict=True))
    nodes=Counter()
    candidate_count=Counter()
    witness_origin_counts=Counter()
    def collect(results):
        for b,count,candidates,origins in results:
            nodes[b]+=count
            if candidates:
                candidate_count[b]+=candidates
            witness_origin_counts.update(origins)
    if workers==1:
        collect(map(replay_archive_chunk,work))
    else:
        with ProcessPoolExecutor(max_workers=workers) as pool:
            collect(pool.map(replay_archive_chunk,work,chunksize=1))
    need(candidate_count=={12:1},"candidate credit count")
    return dict(status="all_n18_topologies_excluded_below_exact_candidate",
                owners=list(B),archive_sha256=sha256(raw).hexdigest(),
                unchecked_orbits=0,orig_census_counts={b:len(rows[b]) for b in B},
                noncandidate_proof_nodes={b:nodes[b] for b in B},
                candidate_orbits=dict(candidate_count),
                noncandidate_witness_origins=dict(witness_origin_counts))


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("census",type=Path)
    p.add_argument("root",type=Path)
    p.add_argument("tree",type=Path)
    p.add_argument("archive",type=Path)
    p.add_argument("--pack-from",type=Path)
    p.add_argument("--receipt",type=Path)
    p.add_argument("--workers",type=int,default=1)
    a=p.parse_args()
    if a.pack_from:
        pack(a.pack_from,a.archive)
    report=replay(a.census,a.root,a.tree,a.archive,a.workers)
    if a.receipt:
        write_json(a.receipt,report)
    print(json.dumps(report,indent=2))
