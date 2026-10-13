"""Fresh n22 root/same-root whole-disk upper/local-isolation interfaces.

Writes only to a new folder. No optimizer is imported or run. Bound source
files and original certificates are preserved. The force/core trees and
catalogue closure have their own replays.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import importlib.util
import json
import shutil
import sys
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
SYN = ROOT.parent
assert __debug__


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    out = args.output.resolve()
    assert not out.exists()
    out.mkdir(parents=True)
    folder = out / "evidence/n22"
    folder.mkdir(parents=True)
    original = SYN / "evidence/n22"
    for name in ("core-system.json", "core-root.json", "candidate-numeric.json"):
        shutil.copy2(original / name, folder / name)
    root = load("fresh_n22_algebraic_interfaces", SYN / "algebraic_roots.py")
    root.EV = out / "evidence"
    rootout = folder / "algebraic-check1"
    rootout.mkdir()
    data, z, rho = root.verify(22, rootout)
    root.upper(22, data, z, rho, rootout)
    local = load("fresh_n22_local_interface", SYN / "local_certificates.py")
    local.ROOT = out
    previous = sys.argv
    try:
        sys.argv = ["local_certificates.py", "--n", "22"]
        local.main()
    finally:
        sys.argv = previous
    target = folder / "local-isolation-certificate.json"
    assert target.read_bytes() == (original / target.name).read_bytes()
    accepted = json.loads((rootout / "root-verified.json").read_text())
    upper = json.loads((rootout / "upper-verified.json").read_text())
    isolation = json.loads(target.read_text())
    assert accepted["verified"] and upper["verified"] and isolation["verified"]
    assert accepted["root_sha256"] == upper["root_sha256"] == isolation["root_sha256"]
    assert upper["same_core_root_entire_disk_upper"] and upper["cover_radius_equals_core_radius"]
    assert (upper["vertices"], upper["edges"], upper["triangles"], upper["caps"]) == (36, 91, 56, 14)
    assert isolation["geometry_dimension"] == isolation["positive_leading_principal_minors"] == 126
    assert F(isolation["isolation_margin"]) == F(7, 50000)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel"))
    report = {"verified": True, "N": 22, "dimension": 252,
              "root_sha256": sha(folder / "core-root.json"),
              "system_sha256": sha(folder / "core-system.json"),
              "root_report_sha256": sha(rootout / "root-verified.json"),
              "upper_report_sha256": sha(rootout / "upper-verified.json"),
              "local_certificate_sha256": sha(target),
              "same_root_entire_closed_disk_upper": True,
              "root_and_geometric_isolation_freshly_replayed": True,
              "no_optimizer_imported": True,
              "root_acceptor_sha256": sha(SYN / "algebraic_roots.py"),
              "local_acceptor_sha256": sha(SYN / "local_certificates.py"),
              "source_sha256": sha(Path(__file__)), "global_optimality_proved": False}
    (out / "INTERFACES.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N22 fresh root/whole closed disk upper/126D isolation interfaces PASS", flush=True)


if __name__ == "__main__":
    main()
