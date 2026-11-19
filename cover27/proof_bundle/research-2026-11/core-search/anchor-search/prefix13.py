"""Replay disjoint minimum-radius intervals of the auxiliary 13-disk search."""
import argparse
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import subprocess

from inner13_tables import generate


def cases(radius,band,radial,first,last):
    for i in range(first,last):
        yield radius,band,radial,i


def run(job,exe,output,angular,budget):
    radius,band,radial,i=job
    key=f"{radius}-{band}-{i:03}"
    table=output/(key+".table")
    log=output/(key+".log")
    generate(table,radius,band,angular,radial,i,i+1)
    p=subprocess.run([str(exe),str(table),str(budget)],capture_output=True,text=True,encoding="utf-8")
    log.write_text(p.stdout+p.stderr,encoding="utf-8")
    nodes=re.search(r"^nodes (\d+) conflicts",p.stdout,re.M)
    if p.returncode not in (0,1) or nodes is None:
        raise ValueError(f"failed {key}: {p.returncode} {p.stderr}")
    if p.returncode==0 and not re.search(r"^excluded$",p.stdout,re.M):
        raise ValueError(f"missing exclusion verdict for {key}")
    result="excluded" if p.returncode==0 else "unresolved"
    print(f"{key} {result} {nodes.group(1)}",flush=True)
    return {"radius":radius,"band":band,"index":i,"nodes":int(nodes.group(1)),
            "state":result,"log":log.name}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("exe",type=Path)
    p.add_argument("output",type=Path)
    p.add_argument("--radius",type=int,required=True)
    p.add_argument("--band",type=int,choices=[0,1],default=0)
    p.add_argument("--first",type=int,default=0)
    p.add_argument("--last",type=int)
    p.add_argument("--angular",type=int,default=360)
    p.add_argument("--radial",type=int,default=96)
    p.add_argument("--jobs",type=int,default=4)
    p.add_argument("--node-limit",type=int,default=150000)
    a=p.parse_args()
    a.output.mkdir(exist_ok=True)
    end=a.last if a.last is not None else max(4,a.radial//4)
    js=list(cases(a.radius,a.band,a.radial,a.first,end))
    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        result=list(pool.map(lambda j:run(j,a.exe.resolve(),a.output,a.angular,a.node_limit),js))
    (a.output/"status.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")


if __name__=="__main__":
    main()
