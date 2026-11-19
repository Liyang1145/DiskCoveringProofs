# SPDX-License-Identifier: MIT
"""Resumable native n=19 force scan. A failure is never a proof decision."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from hashlib import sha256
from pathlib import Path
import argparse
import json

from candidate_energy import verify as check_energy
from check_septagon_force import examine as check_septagons
from compare_census import energy_subgraph, read
from force_prototype import build_tree, graph_data, need, verify_tree

HERE = Path(__file__).resolve().parent


def load_census(directory):
    receipt=json.loads((HERE/"census_receipt.json").read_text())
    need([r["owners"] for r in receipt]==[12,13,14],"missing or repeated owner count")
    rows={}
    for rule in receipt:
        b=rule["owners"]
        a=directory/f"dfs-{b}.json"
        u,_=read(a,b,"dfs")
        v,_=read(directory/f"audit-{b}.json",b,"audit")
        checksum=sha256(json.dumps(u,separators=(",",":")).encode()).hexdigest()
        need(u==v and len(u)==rule["orbits"] and checksum==rule["orbit_sha256"],
             "native census receipt mismatch")
        raw=json.loads(a.read_text())["survivors"]
        need([(tuple(r["faces"]),r["stabilizer"]) for r in raw]==u,
             "noncanonical index ordering")
        rows[b]=[tuple(r["faces"]) for r in raw]
    return rows


def special(directory,rows):
    check_energy()
    key=HERE/"septagon_force.json"
    check_septagons(directory/"dfs-12.json",key)
    septagons={tuple(r["faces"]) for r in json.loads(key.read_text())}
    energy={f for f in rows[12] if energy_subgraph(f)}
    need(len(energy)==34 and len(septagons)==22 and not energy&septagons,
         "ambiguous preceding proof interface")
    return {12:{**{f:"candidate_energy" for f in energy},
                **{f:"septagon_force" for f in septagons}},13:{},14:{}}


def write_json(path,data):
    tmp=path.with_suffix(".pending")
    with tmp.open("w") as f:
        json.dump(data,f,separators=(",",":"))
        f.write("\n")
    tmp.replace(path)


def run_chunk(path,b,start,masks,closed,hints,depth,directions,retry=False):
    old=None
    if retry and path.exists():
        check_chunk(path,b,start,masks,closed,False)
        old=json.loads(path.read_text())["records"]
    out=[]
    for i,faces in enumerate(masks,start):
        prev=old[i-start] if old is not None else None
        if prev is not None and prev["status"]!="unresolved":
            out.append(prev)
            continue
        rec={"index":i,"faces":faces}
        if faces in closed:
            rec["status"]=closed[faces]
        else:
            tree=hints.get((b,i))
            try:
                if tree is not None:
                    counts=verify_tree(b,faces,tree)
                else:
                    tree=build_tree(b,*graph_data(b,faces),depth,directions)
                    counts=verify_tree(b,faces,tree)
            except ArithmeticError as e:
                rec.update(status="unresolved",reason=str(e))
            else:
                rec.update(status="excluded_force",tree=tree,replay=counts)
        out.append(rec)
    write_json(path,{"owners":b,"start":start,"stop":start+len(masks),"records":out,
                     "depth":depth,"directions":directions})
    return sum(r["status"]=="unresolved" for r in out)


def check_chunk(path,b,start,masks,closed,replay):
    return check_records(json.loads(path.read_text()),b,start,masks,closed,replay)


def check_records(d,b,start,masks,closed,replay):
    need(all(type(d[k]) is int for k in ("owners","start","stop"))
         and type(d["records"]) is list,"bad chunk field types")
    need((d["owners"],d["start"],d["stop"],len(d["records"]))==
         (b,start,start+len(masks),len(masks)),"chunk shape mismatch")
    unresolved=[]
    for i,(faces,rec) in enumerate(zip(masks,d["records"],strict=True),start):
        need(type(rec["index"]) is int and type(rec["faces"]) is list
             and all(type(f) is int for f in rec["faces"]),"bad graph index or mask type")
        need((rec["index"],tuple(rec["faces"]))==(i,faces),"chunk orbit mismatch")
        status=rec["status"]
        if status in ("candidate_energy","septagon_force"):
            need(closed.get(faces)==status,"false prior exclusion")
        elif status=="excluded_force":
            counts=rec.get("replay")
            need(rec.get("tree") and isinstance(counts,dict)
                 and set(counts)=={"force","empty","split"}
                 and all(type(x) is int and x>=0 for x in counts.values()),
                 "missing or malformed force proof receipt")
            if replay:
                need(verify_tree(b,faces,rec["tree"])==rec["replay"],"replay mismatch")
        else:
            need(status=="unresolved","bad record status")
            unresolved.append((b,i))
    return unresolved


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("census",type=Path)
    ap.add_argument("output",type=Path)
    ap.add_argument("--workers",type=int,default=4)
    ap.add_argument("--chunk",type=int,default=120)
    ap.add_argument("--depth",type=int,default=5)
    ap.add_argument("--directions",type=int,default=48)
    ap.add_argument("--hints",nargs="*",type=Path,default=[])
    ap.add_argument("--replay-only",action="store_true")
    ap.add_argument("--retry-unresolved",action="store_true",
                    help="regenerate only unresolved entries in existing chunks")
    a=ap.parse_args()
    need(a.workers>=1 and a.chunk>=1 and a.depth>=0 and a.directions>=8,
         "bad scanner parameters")
    need(not (a.replay_only and a.retry_unresolved),"conflicting replay flags")
    rows=load_census(a.census)
    closed=special(a.census,rows)
    a.output.mkdir(parents=True,exist_ok=True)
    hints={}
    for p in a.hints:
        for rec in json.loads(p.read_text()):
            b,i=rec["owners"],rec["index"]
            need(tuple(rec["faces"])==rows[b][i],"hint orbit mismatch")
            hints[b,i]=rec["tree"]
    jobs=[]
    for b,masks in rows.items():
        for start in range(0,len(masks),a.chunk):
            group=masks[start:start+a.chunk]
            path=a.output/f"{b}-{start:05d}-{start+len(group):05d}.json"
            jobs.append((path,b,start,group))
    if not a.replay_only:
        with ProcessPoolExecutor(max_workers=a.workers) as pool:
            running={}
            for path,b,start,group in jobs:
                if path.is_file():
                    if not a.retry_unresolved or not check_chunk(path,b,start,group,closed[b],False):
                        continue  # resumed chunks are verified in the replay below
                local={(b,i):hints[b,i] for i in range(start,start+len(group))
                       if (b,i) in hints}
                fut=pool.submit(run_chunk,path,b,start,group,closed[b],local,a.depth,a.directions,a.retry_unresolved)
                running[fut]=path
            for fut in as_completed(running):
                print(running[fut].name,"done; unresolved",fut.result(),flush=True)
    absent=[]
    unresolved=[]
    checked=0
    with ProcessPoolExecutor(max_workers=a.workers) as pool:
        running={}
        for path,b,start,group in jobs:
            if not path.is_file():
                absent.append(path.name)
            else:
                fut=pool.submit(check_chunk,path,b,start,group,closed[b],True)
                running[fut]=len(group)
        for fut in as_completed(running):
            unresolved.extend(fut.result())
            checked+=running[fut]
    total=sum(map(len,rows.values()))
    need(bool(absent) or checked==total,"did not replay expected total")
    report={"total":total,"replayed":checked,
            "missing_chunks":absent,"unresolved":sorted(unresolved),
            "complete":not absent and not unresolved}
    write_json(a.output/"scan-report.json",report)
    print(json.dumps(report))
    if absent or unresolved:
        raise SystemExit(2)


if __name__=="__main__":
    main()
