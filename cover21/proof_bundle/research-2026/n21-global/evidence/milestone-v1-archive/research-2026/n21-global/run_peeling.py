"""Run exact small census regressions, then n21 family searches.

Limits are development limits only. An interrupted family is recorded pending,
never excluded. The two modes share code, so this is not a fully independent
enumerator pair; geometric induction and further audits remain obligations.
"""
from pathlib import Path
from functools import lru_cache
from math import comb,factorial
import argparse
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
EV = ROOT/"evidence"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


@lru_cache(None)
def labelled(b,i):
    assert b >= 2 and i >= 0
    if b == 2:
        return int(i == 0)
    answer = sum(comb(i,j)*labelled(k,j)*labelled(b-k+1,i-j)
                 for k in range(2,b) for j in range(i+1))
    if i:
        answer += i*(labelled(b+1,i-1)-sum(comb(i-1,j)*labelled(3,j)*labelled(b,i-1-j)
                    for j in range(i)))
    return answer


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def call(out,n,b,constants,mode,limit):
    output = out/f"N{n}-B{b}-{mode}.json"
    log = out/f"N{n}-B{b}-{mode}.log"
    assert not output.exists() and not log.exists(), "No stale result reuse"
    command = [str(ROOT/"peel21"),str(n),str(b),str(output),str(constants["angle_scale"]),
               *map(str,constants["angle_caps"]),str(limit),mode]
    start = time.time()
    with log.open("wb") as target:
        run = subprocess.run(command,stdout=target,stderr=subprocess.STDOUT)
    record = {"N":n,"B":b,"mode":mode,"exit":run.returncode,
              "seconds":time.time()-start,"log_sha256":sha(log)}
    if run.returncode:
        assert not output.exists()
        record["status"] = "pending"
        record["diagnostic_tail"] = log.read_text()[-700:]
        return record,None
    result = json.loads(output.read_text())
    assert result["complete"] and result["N"] == n and result["B"] == b
    assert result["caps"] == constants["angle_caps"]
    record.update(status="complete",calls=result["calls"],surviving_orbits=result["orbits"],
                  output_sha256=sha(output))
    return record,result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--node-limit",type=int,default=1000000)
    parser.add_argument("--boundary",type=int,nargs="*")
    parser.add_argument("--tests-only",action="store_true")
    parser.add_argument("--extended-tests",action="store_true")
    args = parser.parse_args()
    assert sys.platform != "win32", "Use the compiled Linux executable through WSL"
    out = args.output.resolve()
    assert not out.exists()
    out.mkdir(parents=True)
    constants = json.loads((EV/"angle-constants.json").read_text())
    assert constants["verified"]
    sourcehash = sha(ROOT/"peel21.cpp")
    tests = []
    test_pairs = [(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0)]
    if args.extended_tests:
        test_pairs += [(3,i) for i in range(4,10)]+[(4,3),(4,4),(5,2)]
    for b,i in test_pairs:
        rs,records = [],[]
        for mode in ("noscreen","audit-noscreen"):
            record,result = call(out,b+i,b,constants,mode,0)
            assert result is not None
            assert result["rooted"]*factorial(i) == labelled(b,i)
            mass = sum(2*b*factorial(i)//v["stabilizer"] for v in result["survivors"])
            assert all(2*b*factorial(i)%v["stabilizer"] == 0 for v in result["survivors"])
            assert mass == labelled(b,i)
            rs.append(result)
            records.append(record)
        assert rs[0]["survivors"] == rs[1]["survivors"]
        tests.append({"B":b,"I":i,"labelled":labelled(b,i),"orbits":rs[0]["orbits"],"runs":records})
        print("SMALL EXACT CENSUS",b,i,"PASS",flush=True)
    # Failure must not be accepted as a complete family.
    limited,none = call(out,23,3,constants,"noscreen",1)
    assert none is None and limited["status"] == "pending"
    families = []
    if not args.tests_only:
        boundaries = args.boundary if args.boundary else list(range(20,11,-1))
        assert all(12 <= b <= 20 for b in boundaries)
        for b in boundaries:
            runs,results = [],[]
            for mode in ("dfs","audit"):
                record,result = call(out,21,b,constants,mode,args.node_limit)
                runs.append(record)
                results.append(result)
                print("N21 FAMILY",b,mode,record["status"],
                      record.get("surviving_orbits","not completed"),flush=True)
            if all(v is not None for v in results):
                assert results[0]["survivors"] == results[1]["survivors"]
                status = "complete-matching-survivor-sets"
            else:
                status = "pending"
            families.append({"B":b,"I":21-b,"status":status,"runs":runs})
    summary = {"verified_small_regressions":True,"tests":tests,"node_limit_rejected":True,
               "families":families,"source_sha256":sourcehash,"constants_sha256":sha(EV/"angle-constants.json"),
               "global_optimality_proved":False,
               "scope":"two traversal/closure modes in one new source, not two independent external implementations"}
    (out/"SUMMARY.json").write_text(json.dumps(summary,indent=2),encoding="utf8")
    print("PEELING STAGE SUMMARY SAVED; global optimality remains incomplete",flush=True)


if __name__ == "__main__":
    main()
