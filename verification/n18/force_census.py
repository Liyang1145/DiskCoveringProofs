# SPDX-License-Identifier: MIT
"""Resumable native n=18 force scan. A failure is never a proof decision."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from hashlib import sha256
from pathlib import Path
import argparse
import json

from candidate_data_replay import check as verify_candidate
from candidate_force import f
from compare_census import candidate_code, load

HERE = Path(__file__).resolve().parent
need=f.need
graph_data=f.graph_data
build_tree=f.build_tree
verify_tree=f.verify_tree


def load_census(directory):
    receipt=json.loads((HERE/"census_receipt.json").read_text())["results"]
    need([r["owners"] for r in receipt]==[11,12,13],"missing or repeated owner count")
    rows={}
    for rule in receipt:
        b=rule["owners"]
        u,_=load(directory/f"dfs-{b}.json",b,"dfs")
        v,_=load(directory/f"audit-{b}.json",b,"audit")
        checksum=sha256(json.dumps(u,separators=(",",":")).encode()).hexdigest()
        need(u==v and len(u)==rule["orbits"] and checksum==rule["orbit_sha256"],
             "native census receipt mismatch")
        rows[b]=[fs for fs,_ in u]
    return rows


def special(directory,rows,root,tree):
    closed={b:{} for b in rows}
    if 12 in rows:
        need(root is not None and tree is not None,"B12 scan needs pinned candidate proof inputs")
        candidate=verify_candidate(root,directory/"dfs-12.json",tree)
        need(candidate["status"]=="candidate_orbit_only_full_angle_domain_excluded",
             "candidate proof did not close")
        key=candidate_code()[0]
        need(rows[12].count(key)==1,"missing or repeated candidate orbit")
        closed[12][key]="verified_candidate_orbit"
    return closed


def write_json(path,data):
    from tempfile import NamedTemporaryFile
    with NamedTemporaryFile(mode="w", prefix=path.name+".",
                            suffix=".pending", dir=path.parent, delete=False) as f:
        tmp=Path(f.name)
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
    return check_chunk_data(json.loads(path.read_text()),b,start,masks,closed,replay)


def check_chunk_data(d,b,start,masks,closed,replay):
    need((d["owners"],d["start"],d["stop"],len(d["records"]))==
         (b,start,start+len(masks),len(masks)),"chunk shape mismatch")
    unresolved=[]
    for i,(faces,rec) in enumerate(zip(masks,d["records"],strict=True),start):
        need((rec["index"],tuple(rec["faces"]))==(i,faces),"chunk orbit mismatch")
        status=rec["status"]
        if status=="verified_candidate_orbit":
            need(closed.get(faces)==status,"false prior exclusion")
        elif status=="excluded_force":
            need(rec.get("tree"),"missing force proof")
            if replay:
                need(verify_tree(b,faces,rec["tree"])==rec["replay"],"replay mismatch")
        elif status=="excluded_force_original_labels":
            need(rec.get("witness_nodes") and rec.get("source_faces"),"missing original-label witness")
            if replay:
                from noncandidate_data_replay import verify_loaded_witness
                need(verify_loaded_witness(b,faces,rec["source_faces"],rec["witness_nodes"])
                     ==rec["replay"],"original-label replay mismatch")
        else:
            need(status=="unresolved","bad record status")
            unresolved.append((b,i))
    return unresolved


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("census",type=Path)
    ap.add_argument("output",type=Path)
    ap.add_argument("--workers",type=int,default=1)
    ap.add_argument("--owners",type=int,choices=(11,12,13),nargs="+",default=[11,12,13])
    ap.add_argument("--candidate-root",type=Path)
    ap.add_argument("--candidate-tree",type=Path)
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
    need(len(a.owners)==len(set(a.owners)),"duplicate owner count")
    rows={b:rows[b] for b in sorted(a.owners)}
    closed=special(a.census,rows,a.candidate_root,a.candidate_tree)
    a.output.mkdir(parents=True,exist_ok=True)
    hints={}
    for p in a.hints:
        for rec in json.loads(p.read_text()):
            b,i=rec["owners"],rec["index"]
            need(b in rows and type(i) is int and 0<=i<len(rows[b]),"invalid hint index")
            need(tuple(rec["faces"])==rows[b][i] and (b,i) not in hints,"hint orbit mismatch")
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
    report={"owners":list(rows),"total":total,"replayed":checked,
            "missing_chunks":absent,"unresolved":sorted(unresolved),
            "complete":not absent and not unresolved,
            "all_topologies_closed":list(rows)==[11,12,13] and not absent and not unresolved}
    write_json(a.output/("scan-report-"+"-".join(map(str,rows))+".json"),report)
    print(json.dumps(report))
    if absent or unresolved:
        raise SystemExit(2)


if __name__=="__main__":
    main()
