#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Replay native topology, attainment, and complete n=17 lower certificates."""
from argparse import ArgumentParser
from contextlib import redirect_stdout
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import sys

import candidate_data_replay as c
import noncandidate_data_replay as ext
import replay_force as own
from check_native_n17_census import census, EXPECTED
from check_native_n17_root import DIGEST, geometry, isolate

CERTIFICATES = (
    "B11-force.json", "B12-force.json", "B12-deep-force.json",
    "B13-force.json", "B13-deep-force.json",
    "B12-pairs-force.json", "B13-pairs-force.json",
)
RADIUS_LO = "0.298531589256428059869843774423980703734387603913740470124900"
RADIUS_HI = "0.298531589256428059869843774423980703734387603913740470124901"


def check(root,candidate_tree,forest):
    source=Path(root).read_bytes()
    c.f.need(sha256(source).hexdigest()==DIGEST,"bad candidate root digest")
    z=isolate(json.loads(source))
    geometry(z)
    runs=Path(__file__).resolve().parent/"runs"
    paths=[runs/name for name in CERTIFICATES]
    candidate_id=(12,629)
    all_noncandidate={(b,i) for b,(total,_,_) in EXPECTED.items()
                      for i in range(total)}-{candidate_id}
    with TemporaryDirectory(prefix="verify-n17-global-") as temp:
        directory=Path(temp)
        with redirect_stdout(sys.stderr):
            census(directory)
            paid=own.check(directory,paths,False)
        missing={}
        for b,i in sorted(all_noncandidate-set(paid)):
            missing.setdefault(b,[]).append(i)
        assisted=ext.check(directory,forest,True,missing)
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
    p.add_argument("noncandidate_forest")
    a=p.parse_args()
    print(json.dumps(check(a.root,a.candidate_tree,a.noncandidate_forest),indent=2))
