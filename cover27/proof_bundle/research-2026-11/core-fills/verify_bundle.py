"""Replay the core catalogue and area bounds, with an optional auxiliary search."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory


ROOT=Path(__file__).resolve().parent
SRC=ROOT/"anchor-search"
TEST_RADIUS=338_900_000
NORM_CEILING=911_811_049
NODE_TOTAL=1_296_088


def invoke(*args):
    subprocess.run(list(map(str,args)),cwd=ROOT,check=True)


def same(path):
    if path.read_bytes()!=(ROOT/path.name).read_bytes():
        raise ValueError(f"replayed file differs from {path.name}")


def check_manifest():
    manifest=json.loads((ROOT/"MANIFEST.json").read_text(encoding="utf-8"))
    for item in manifest["files"]:
        raw=(ROOT/item["path"]).read_bytes()
        if len(raw)!=item["bytes"] or sha256(raw).hexdigest()!=item["sha256"]:
            raise ValueError(f"file integrity check failed for {item['path']}")


def search_aux13(tmp,jobs):
    from inner13_tables import generate
    invoke(sys.executable,"-B",SRC/"verify_core_count.py")
    program=tmp/("core13.exe" if os.name=="nt" else "core13")
    env={**os.environ,"TEMP":str(tmp),"TMP":str(tmp),"TMPDIR":str(tmp)}
    subprocess.run(["g++","-std=c++20","-O3","-DCOVER27_DISKS=13","-DCOVER27_BOUNDARY=10",
                    str(SRC/"interval_search.cpp"),"-o",str(program)],cwd=tmp,env=env,check=True)

    def verify_interval(case):
        band,index=case
        table=tmp/f"band-{band}-{index:02d}.txt"
        generate(table,TEST_RADIUS,band,360,96,index,index+1)
        proc=subprocess.run([str(program),str(table),"0"],capture_output=True,
                            text=True,encoding="utf-8",check=True)
        count=re.search(r"^nodes ([0-9]+) conflicts ",proc.stdout,re.M)
        if count is None or not re.search(r"^excluded$",proc.stdout,re.M):
            raise ValueError(f"unresolved auxiliary interval {case}")
        return int(count[1])

    cases=[(band,index) for band in (0,1) for index in range(24)]
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        total=sum(pool.map(verify_interval,cases))
    if total!=NODE_TOTAL:
        raise ValueError(f"the auxiliary search visits {total} nodes, expected {NODE_TOTAL}")
    print(f"PASS: all {len(cases)} auxiliary intervals excluded at radius {TEST_RADIUS}/1e9 in {total} nodes.",flush=True)
    u=Fraction(230796,10**6)
    q=Fraction(TEST_RADIUS,10**9)
    if u*(1+1/q)>=Fraction(NORM_CEILING,10**9):
        raise ValueError("invalid D1 ceiling")
    print(f"PASS B=14: the auxiliary lower bound gives D1 < {NORM_CEILING}/1e9.",flush=True)


def replay(tmp):
    from verify_core_fills import verify as enumerate_fills
    from verify_core_fill_count import verify as count_fills
    from verify_core_degree_join import verify as join_fills,write_groups
    from verify_annulus_angles import verify as check_annulus_angles

    annuli=ROOT/"B14-ten-ring.json"
    degrees=tmp/"B14-residual-degrees.json"
    recatalog=tmp/annuli.name
    invoke("node",ROOT/"verify_boundary14_degree_cap.js",degrees)
    invoke(sys.executable,"-B",SRC/"verify_b14_ten_ring.py",degrees,"--output",recatalog)
    same(recatalog)
    fills=tmp/"B14-core-fills.json"
    result=enumerate_fills()
    count_fills(len(result["triangulations"]))
    fills.write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8")
    same(fills)

    supports=tmp/"B14-degree-area-supports.json"
    invoke("node",SRC/"verify_core_degree_area.js",annuli,supports)
    same(supports)
    groups=tmp/"B14-core-degree-groups.json"
    write_groups(groups,fills)
    same(groups)
    core_area=tmp/"B14-core-disk-area.json"
    invoke("node",SRC/"verify_core_disk_area.js",groups,core_area)
    same(core_area)
    angles=tmp/"B14-annulus-angles.json"
    records=check_annulus_angles(annuli)
    angles.write_text(json.dumps(records,separators=(",",":"))+"\n",encoding="utf-8")
    same(angles)
    angular={row["owner_norm_floor"]//1000:row["placements_per_annulus"] for row in records}
    report=tmp/"B14-core-degree-join.json"
    data=join_fills(annuli,fills,supports,core_area,angular)
    report.write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf-8")
    same(report)
    print("PASS: the core-fill catalogue, area comparisons, and angular exclusions reproduce.",flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--replay-aux13",action="store_true")
    p.add_argument("--only-aux13",action="store_true")
    p.add_argument("--global-lower",action="store_true")
    p.add_argument("--jobs",type=int,default=6)
    a=p.parse_args()
    if a.jobs<1:
        raise ValueError("jobs must be positive")
    check_manifest()
    if a.global_lower:
        invoke(sys.executable,"-B",ROOT/"verify_global_lower.py")
    sys.path.insert(0,str(SRC))
    run_aux=a.replay_aux13 or a.only_aux13
    with TemporaryDirectory(prefix="replay-",dir=ROOT if run_aux else None) as folder:
        tmp=Path(folder)
        if not a.only_aux13:
            replay(tmp)
        if run_aux:
            search_aux13(tmp,a.jobs)
