"""Fresh finite peeling regressions and bounded original-family search.

No node-limit result is accepted as complete; no prior snapshot is changed.
Source shares a common mathematical kernel, not independent proof implementations.
"""
from pathlib import Path
from functools import lru_cache
from math import comb,factorial
import argparse
import hashlib
import json
import subprocess
import time

ROOT=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


@lru_cache(None)
def labelled(b,i):
    if b==2:
        return int(i==0)
    a=sum(comb(i,j)*labelled(k,j)*labelled(b-k+1,i-j) for k in range(2,b) for j in range(i+1))
    if i:
        a+=i*(labelled(b+1,i-1)-sum(comb(i-1,j)*labelled(3,j)*labelled(b,i-1-j) for j in range(i)))
    return a


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def run(output,n,b,mode,limit,constants):
    target=output/f"N{n}-B{b}-{mode}.json"
    logfile=output/f"N{n}-B{b}-{mode}.log"
    assert not target.exists() and not logfile.exists()
    command=[str(ROOT/"peel_synthesis"),str(n),str(b),str(target),
             str(constants["angle_scale"]),*map(str,constants["angle_caps"]),str(limit),mode]
    started=time.time()
    with logfile.open("wb") as stream:
        process=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT)
    info={"N":n,"B":b,"mode":mode,"exit":process.returncode,"seconds":time.time()-started,
          "log_sha256":sha(logfile),"source_sha256":sha(ROOT/"peel_synthesis.cpp")}
    if process.returncode:
        assert not target.exists()
        info["status"]="pending"
        info["tail"]=logfile.read_text()[-400:]
        return info,None
    data=json.loads(target.read_text())
    assert data["complete"] and data["N"]==n and data["B"]==b and data["caps"]==constants["angle_caps"]
    info.update(status="complete",calls=data["calls"],orbits=data["orbits"],output_sha256=sha(target))
    return info,data


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--n",type=int,default=21)
    parser.add_argument("--boundary",type=int,nargs="*",default=[])
    parser.add_argument("--limit",type=int,default=150000000)
    parser.add_argument("--extended-tests",action="store_true")
    args=parser.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    if args.n==21:
        source=ROOT.parent/"n21-global/evidence/angle-constants.json"
    else:
        source=ROOT/"evidence/core-reduction/constants"/f"n{args.n}.json"
    constants=json.loads(source.read_text())
    assert constants["verified"]
    tests=[]
    test_pairs=[(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1),(4,2),(5,1),(6,0)]
    if args.extended_tests:
        test_pairs += [(3,i) for i in range(6,10)]+[(4,3),(4,4),(5,2)]
    for b,i in test_pairs:
        results=[];reports=[]
        for mode in ("noscreen","audit-noscreen"):
            info,data=run(args.output,b+i,b,mode,0,constants)
            assert data is not None and data["rooted"]*factorial(i)==labelled(b,i)
            assert sum(2*b*factorial(i)//r["stabilizer"] for r in data["survivors"])==labelled(b,i)
            results.append(data);reports.append(info)
        assert results[0]["survivors"]==results[1]["survivors"]
        tests.append({"B":b,"I":i,"labelled":labelled(b,i),"orbits":results[0]["orbits"],"runs":reports})
        print("SYNTHESIS PEEL SMALL",b,i,"PASS",flush=True)
    families=[]
    for b in args.boundary:
        assert 3<=b<args.n<=25
        rs=[];records=[]
        for mode in ("dfs","audit"):
            info,data=run(args.output,args.n,b,mode,args.limit,constants)
            records.append(info);rs.append(data)
            print("N",args.n,"family",b,mode,info["status"],info.get("orbits","pending"),flush=True)
        complete=all(r is not None for r in rs)
        if complete:
            assert rs[0]["survivors"]==rs[1]["survivors"]
        families.append({"B":b,"I":args.n-b,"complete_matching":complete,"runs":records})
        (args.output/"SUMMARY.json").write_text(json.dumps({"verified_small_cases":True,"tests":tests,
          "families":families,"N":args.n,"global_optimality_proved":False,
          "constants_sha256":sha(source),"kernel_sha256":sha(ROOT/"peel_synthesis.cpp")},indent=2),encoding="utf8")
    if not args.boundary:
        (args.output/"SUMMARY.json").write_text(json.dumps({"verified_small_cases":True,"tests":tests,"N":args.n,
          "families":[],"global_optimality_proved":False,"kernel_sha256":sha(ROOT/"peel_synthesis.cpp")},indent=2),encoding="utf8")


if __name__=="__main__":
    main()
