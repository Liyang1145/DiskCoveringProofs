"""Re-execute n21 achieved milestones into a new folder; not a global replay."""
from pathlib import Path
import argparse
import importlib
import json
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    assert not output.exists()
    output.mkdir(parents=True)
    for name in ("core-root.json","core-system.json","candidate-numeric.json"):
        shutil.copy2(ROOT/"evidence"/name,output/name)
    root = importlib.import_module("root_certificate")
    root.EV = output
    data,z,rho = root.verify()
    root.upper(data,z,rho)
    local = importlib.import_module("local_isolation")
    local.EV = output
    local.main()
    candidate = importlib.import_module("candidate_tree")
    # Original tree bindings are verified against original immutable milestone
    # reports; no source certificate or original timing-dependent report is edited.
    candidate.verify(ROOT/"evidence/candidate-tree-round2.json.gz",
                     report_path=output/"candidate-tree-verified.json")
    result = subprocess.run([sys.executable,"-B",str(ROOT/"six_core_exclusion.py"),"--replay"],
                            stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    print(result.stdout,end="")
    assert result.returncode == 0
    shutil.copy2(ROOT/"evidence/six-core-exclusion/REPLAY.json",output/"six-core-replayed.json")
    negative = subprocess.run([sys.executable,"-B",str(ROOT/"negative_checks.py")],
                              stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    print(negative.stdout,end="")
    assert negative.returncode == 0
    shutil.copy2(ROOT/"evidence/negative-checks.json",output/"negative-checks.json")
    bound = subprocess.run([sys.executable,"-B",str(ROOT/"freeze_milestone.py")],
                           stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    print(bound.stdout,end="")
    assert bound.returncode == 0
    (output/"REPLAY.json").write_text(json.dumps({
        "verified":True,"scope":"achieved n21 milestones only","global_optimality_proved":False,
        "remaining_families":[[12,9],[13,8],[14,7]]
    },indent=2),encoding="utf8")
    print("N21 MILESTONES FRESHLY REPLAYED; GLOBAL OPTIMALITY STILL INCOMPLETE",flush=True)


if __name__ == "__main__":
    main()
