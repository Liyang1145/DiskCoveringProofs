"""Replay the five normalized branches at a common radius."""
from pathlib import Path
import subprocess

root=Path(__file__).resolve().parent


def run_checks():
    subprocess.run(["node",str(root/"verify_wheel_core.js")],cwd=root,check=True)
    subprocess.run(["node",str(root/"verify_boundary14_shared_angles_229360.js")],cwd=root,check=True)
    subprocess.run(["node",str(root/"verify_apex27_b16.js"),"b16"],cwd=root,check=True)
    subprocess.run(["node",str(root/"anchor-search"/"verify_translated_core.js")],cwd=root,check=True)
    subprocess.run(["node",str(root/"verify_apex27_b16.js"),"b17"],cwd=root,check=True)
    print("PASS: conditional tests cover all five owner counts at U=0.224645.")


if __name__=="__main__":
    run_checks()
