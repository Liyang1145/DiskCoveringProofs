#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Replay native topology, attainment, and complete n=17 lower certificates."""
from argparse import ArgumentParser
from contextlib import redirect_stdout
from hashlib import sha256
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import sys

import candidate_data_replay as c
import noncandidate_data_replay as ext
import replay_force as own
from check_native_n17_census import census, CAPS, EXPECTED
from check_native_n17_root import DIGEST, geometry, isolate

CERTIFICATES = (
    "B11-force.json", "B12-force.json", "B12-deep-force.json",
    "B13-force.json", "B13-deep-force.json",
    "B12-pairs-force.json", "B13-pairs-force.json",
)
FINAL_CERTIFICATE = "B12-final-pairs-force.json"
RADIUS_LO = "0.298531589256428059869843774423980703734387603913740470124900"
RADIUS_HI = "0.298531589256428059869843774423980703734387603913740470124901"


def check(root,candidate_tree,forest=None):
    original = c.f.CAPS,c.f.PREC,c.f.ROOT_PREC
    c.f.CAPS,c.f.PREC,c.f.ROOT_PREC = CAPS,10**15,10**24
    c.f.support.cache_clear()
    c.f.chord_support.cache_clear()
    try:
        return replay(root,candidate_tree,forest)
    finally:
        c.f.CAPS,c.f.PREC,c.f.ROOT_PREC = original
        c.f.support.cache_clear()
        c.f.chord_support.cache_clear()


def replay(root,candidate_tree,forest):
    source=Path(root).read_bytes()
    c.f.need(sha256(source).hexdigest()==DIGEST,"bad candidate root digest")
    z=isolate(json.loads(source))
    geometry(z)
    runs=Path(__file__).resolve().parent/"runs"
    paths=[runs/name for name in CERTIFICATES]
    final_path=runs/FINAL_CERTIFICATE
    if final_path.is_file():
        paths.append(final_path)
    else:
        c.f.need(forest is not None,"missing final native archive and no legacy forest supplied")
    candidate_id=(12,629)
    all_noncandidate={(b,i) for b,(total,_,_) in EXPECTED.items()
                      for i in range(total)}-{candidate_id}
    with TemporaryDirectory(prefix="verify-n17-global-") as temp:
        directory=Path(temp)
        with redirect_stdout(sys.stderr):
            census(directory)
            paid=own.check(directory,paths,forest is None)
        missing={}
        for b,i in sorted(all_noncandidate-set(paid)):
            missing.setdefault(b,[]).append(i)
        if missing:
            c.f.need(forest is not None,"incomplete native lower proof")
            assisted=ext.check(directory,forest,True,missing)
        else:
            assisted={"status":"not_needed","count":0,"matches":[]}
        special=c.check(root,directory/"n17-B12.json",candidate_tree,True)
    assisted_ids={(entry["owners"],entry["index"]) for entry in assisted["matches"]}
    c.f.need(not paid.keys()&assisted_ids and set(paid)|assisted_ids==all_noncandidate,
             "incomplete or duplicate noncandidate proof coverage")
    c.f.need(special["status"]=="candidate_orbit_only_full_angle_domain_excluded",
             "candidate complement not excluded")
    return {
        "n":17, "status":"exact_global_optimality_native_checked",
        "exact":"sqrt(t), coordinate 82 of the unique n17 boxed integer-polynomial root",
        "strict_radius_bracket":[RADIUS_LO,RADIUS_HI],
        "fresh_generated_noncandidate_orbits":len(paid),
        "data_assisted_noncandidate":assisted,
        "data_assisted_candidate":special,
        "fresh_generated_certificate_sha256":{p.name:sha256(p.read_bytes()).hexdigest()
                                              for p in paths},
    }


if __name__=="__main__":
    p=ArgumentParser(description=__doc__)
    p.add_argument("root")
    p.add_argument("candidate_tree")
    p.add_argument("noncandidate_forest",nargs="?",help="legacy fallback for missing native archives")
    a=p.parse_args()
    print(json.dumps(check(a.root,a.candidate_tree,a.noncandidate_forest),indent=2))
