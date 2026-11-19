# SPDX-License-Identifier: MIT
"""Read fixed n19 proof chunks from deterministic gzip JSONL, without extraction."""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from hashlib import sha256
from pathlib import Path
import argparse
import gzip
import json

from force_census import load_census, special, check_records, need

CHUNK=120
MAX_LINE=8*1024*1024
HERE=Path(__file__).resolve().parent


def expected(b, rows):
    for start in range(0,len(rows),CHUNK):
        masks=rows[start:start+CHUNK]
        yield start,masks,f"{b}-{start:05d}-{start+len(masks):05d}.json"


def data_line(raw):
    need(0<len(raw)<=MAX_LINE and raw.endswith(b"\n"),"missing or oversized chunk line")
    def unique(pairs):
        obj=dict(pairs)
        need(len(obj)==len(pairs),"duplicate JSON object key")
        return obj
    return json.loads(raw,object_pairs_hook=unique)


def pack(b,rows,closed,chunks,archive):
    part=archive.with_suffix(".pending")
    with part.open("wb") as raw:
        with gzip.GzipFile(filename="",fileobj=raw,mode="wb",mtime=0,compresslevel=9) as f:
            for start,masks,name in expected(b,rows):
                with (chunks/name).open("rb") as chunk:
                    data=data_line(chunk.readline(MAX_LINE+1))
                    need(chunk.read(1)==b"","extra chunk data")
                need(not check_records(data,b,start,masks,closed,False),"unresolved source rows")
                f.write(json.dumps(data,sort_keys=True,separators=(",",":")).encode()+b"\n")
    part.replace(archive)


def exact_chunk(data,b,start,masks,closed):
    need(not check_records(data,b,start,masks,closed,True),"unresolved archived rows")
    kinds=Counter()
    trees=Counter()
    for rec in data["records"]:
        kinds.update((rec["status"],))
        trees.update(rec.get("replay",{}))
    return kinds,trees


def replay(census,archives,workers,chunks=None):
    rows=load_census(census)
    known=special(census,rows)
    report=[]
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for b,masks in rows.items():
            archive=archives/f"force-b{b}.jsonl.gz"
            if chunks is not None:
                pack(b,masks,known[b],chunks,archive)
            need(archive.stat().st_size <= 64*1024*1024,"oversized compressed archive")
            tasks=[]
            with gzip.open(archive,"rb") as f:
                for start,group,_ in expected(b,masks):
                    data=data_line(f.readline(MAX_LINE+1))
                    tasks.append(pool.submit(exact_chunk,data,b,start,group,known[b]))
                need(f.read(1)==b"","unexpected trailing archive data")
            kinds=Counter()
            trees=Counter()
            for task in tasks:
                k,t=task.result()
                kinds.update(k);trees.update(t)
            need(sum(kinds.values())==len(masks),"archived orbit coverage mismatch")
            with archive.open("rb") as f:
                digest=sha256(f.read()).hexdigest()
            row={"owners":b,"orbits":len(masks),"by_certificate":dict(kinds),
                 "force_tree_nodes":dict(trees),
                 "sha256":digest}
            report.append(row)
            print(json.dumps(row,sort_keys=True),flush=True)
    need(sum(x["orbits"] for x in report)==23535,"incorrect complete graph total")
    return report


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("census",type=Path)
    p.add_argument("--archives",type=Path,default=HERE)
    p.add_argument("--pack",type=Path,help="write deterministic archives from completed chunks before replay")
    p.add_argument("--workers",type=int,default=4)
    a=p.parse_args()
    need(a.workers>=1,"bad worker count")
    if a.pack:
        a.archives.mkdir(exist_ok=True,parents=True)
    replay(a.census,a.archives,a.workers,a.pack)
