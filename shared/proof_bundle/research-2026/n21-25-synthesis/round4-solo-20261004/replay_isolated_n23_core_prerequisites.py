"""Fresh N23 root, same-root upper, local isolation and whole-angle replay.

Original routines and assets are not modified. The root/upper routine's input
directory is explicitly set in this process and recorded in the new ledger.
This proves only the specified core theorem, not arbitrary-type containment.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from math import isqrt
import argparse
import gzip
import hashlib
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
SYN = ROOT.parent
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from replay_candidate import local
import exact_graph as exact

assert __debug__


def isolation(data, root):
    gamma, lam, nu, radius = 500, F(1, 2000), F(1, 100), F(3, 50)
    g, b, edges = data["G"], data["B"], data["edges"]
    m, q = len(edges), 10**15
    x = [F(int(v), int(root["Qx"])) for v in root["xnum"]]
    a = []
    for value in x:
        z = value*q
        a.append((2*z.numerator+z.denominator)//(2*z.denominator))
    rho, eps, buffer = F(1, 10**80), F(2, q), F(1, 10**8)
    assert all(abs(F(a[j], q)-x[j])+rho <= eps
               for j in list(range(g))+list(range(g+1, len(x))))
    assert all(0 < value-rho < value+rho < F(1, 10)
               for value in x[g+1:g+1+m])
    assert all(-nu < value-rho < value+rho < 0 for value in x[g+1+m:])
    points = [[q, 0]]+[a[2*j:2*j+2] for j in range(g//2)]
    jac, weights = [], []
    lap, degree = [[0]*g for _ in range(g)], Counter()
    for k, (u, v) in enumerate(edges):
        degree.update((u, v))
        row = [0]*g
        for axis in (0, 1):
            for node, sign in ((u, 1), (v, -1)):
                if node:
                    j = 2*(node-1)+axis
                    row[j] += 2*sign*(points[u][axis]-points[v][axis])
                    for other, osign in ((u, 1), (v, -1)):
                        if other:
                            lap[j][2*(other-1)+axis] += a[g+1+k]*sign*osign
        jac.append(row)
        weights.append(a[g+1+k]**2)
    nq = nu*q
    assert nq.denominator == 1
    for node in range(1, b):
        row = [0]*g
        for axis in (0, 1):
            j = 2*(node-1)+axis
            row[j] = 2*points[node][axis]
            lap[j][j] += a[g+1+m+node-1]
        jac.append(row)
        weights.append(nq.numerator**2)
    assert sum(value*value for row in jac for value in row) < 144*q*q
    assert max(weights)*100 < q*q
    structural_entries = 4*m+2*(b-1)
    da = 4*(isqrt(structural_entries)+1)*eps
    error = (2*max(degree.values())+1)*eps+gamma*(
        F(1, 100)*(24+da)*da+eps/4*(12+da)**2)
    assert error < buffer
    den = q**4
    h = [[lap[i][j]*q**3+gamma*sum(
        weights[k]*jac[k][i]*jac[k][j] for k in range(len(jac)))
        for j in range(g)] for i in range(g)]
    for i in range(g):
        diff = (buffer+(lam if i < 2*(b-1) else 0))*den
        assert diff.denominator == 1
        h[i][i] -= diff.numerator
    previous, hashes = 1, []
    for k in range(g):
        pivot = h[k][k]
        assert pivot > 0, ("non-positive isolation pivot", k)
        hashes.append(hashlib.sha256(
            pivot.to_bytes((pivot.bit_length()+7)//8, "big")).hexdigest())
        for i in range(k+1, g):
            for j in range(i, g):
                value, remainder = divmod(
                    pivot*h[i][j]-h[i][k]*h[k][j], previous)
                assert not remainder
                h[i][j] = h[j][i] = value
        previous = pivot
        if (k+1) % 20 == 0:
            print("N23 fresh exact local-isolation pivots", k+1, "/", g, flush=True)
    gap = lam-2*gamma*nu**2*radius**2
    assert gap > 0
    return {
        "verified": True, "N": 23,
        "scope": "active-core anchor isolation only; not all topologies or all angles",
        "geometry_dimension": g, "positive_leading_principal_minors": g,
        "gamma": gamma, "lambda": str(lam), "nu": str(nu),
        "anchor_radius": str(radius), "isolation_margin": str(gap),
        "matrix_perturbation_bound": str(error), "principal_minor_binary_sha256": hashes,
        "global_optimality_proved": False,
    }


def main():
    ap = argparse.ArgumentParser()
    for name in ("inputs", "assets", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    inputs, assets, output = args.inputs.resolve(), args.assets.resolve(), args.output.resolve()
    assert all(path.is_relative_to(ROOT) for path in (inputs, assets, output))
    assert not output.exists()
    restored = read(assets / "VERIFIED.json")
    assert restored["verified"] and restored["schema"] == "isolated-N23-nonstrict-core-exact-archive-assets-v1"
    assert restored["source_sha256"] == sha(ROOT / "recover_n23_nonstrict_core_assets.py")
    frozen = dict(restored["frozen_files"])
    for path, expected in frozen.items():
        assert sha(path) == expected
    folder = inputs / "n23"
    systempath, rootpath = folder / "core-system.json", folder / "core-root.json"
    localpath, treepath = assets / "local-isolation-certificate.json", assets / "core-angle-tree.json.gz"
    constantspath = SYN / "evidence/core-reduction/constants/n23.json"
    data, root, oldlocal, constants = map(read, (systempath, rootpath, localpath, constantspath))
    assert (data["N"], data["B"], data["G"], data["D"]) == (23, 15, 120, 234)
    assert root["system_sha256"] == sha(systempath)
    assert oldlocal["root_sha256"] == sha(rootpath)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    rootroutine = SYN / "algebraic_roots.py"
    localroutine = SYN / "local_certificates.py"
    for path in (Path(__file__), assets / "VERIFIED.json", inputs / "VERIFIED.json",
                 systempath, rootpath, folder / "candidate-numeric.json",
                 rootroutine, localroutine, SYN.parent / "n21-global/root_certificate.py",
                 SYN.parent / "n13-global/independent_checks.py",
                 localpath, treepath, constantspath, HIGH / "replay_candidate.py",
                 HIGH / "exact_graph.py", Path(exact.kernel.__file__)):
        frozen[str(path.resolve())] = sha(path)
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": 23, "B": 15, "explicit_original_root_upper_input_directory": str(inputs),
        "explicit_isolated_historical_tree_local_directory": str(assets),
        "root_upper_routines_reused_not_sources_rewritten": True, "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    spec = importlib.util.spec_from_file_location("explicit_isolated_root_upper", rootroutine)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    # This is a recorded input-path setting in a private module instance,
    # not a change to original evidence or to any running proof process.
    module.EV = inputs
    freshdata, z, rho = module.verify(23, output)
    assert freshdata == data
    oldroot = read(assets / "root-verified.json")
    freshroot = read(output / "root-verified.json")
    assert freshroot == oldroot
    module.upper(23, freshdata, z, rho, output)
    assert read(output / "upper-verified.json") == read(assets / "upper-verified.json")
    freshlocal = isolation(data, root)
    freshlocal["root_sha256"] = sha(rootpath)
    for key, value in freshlocal.items():
        assert oldlocal[key] == value, ("local theorem replay differs", key)
    freshlocal["source_sha256"] = sha(Path(__file__))
    freshlocal["original_local_routine_sha256"] = sha(localroutine)
    freshlocal["original_local_certificate_sha256"] = sha(localpath)
    publish(output / "FRESH-LOCAL-ISOLATION.json", freshlocal)
    with gzip.open(treepath, "rt", encoding="utf8") as stream:
        tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
    B = data["B"]
    coreN = data["G"]//2+1-B-len(data["active_faces"])
    masks = sorted(sum(1 << (data["center_core_nodes"][v]-B) for v in face)
                   for face in data["active_faces"])
    assert tree["complete"] and not tree["pending"]
    assert (tree["N"], tree["B"], tree["core_centers"], tree["faces"]) == (23, B, coreN, masks)
    assert tree["root_sha256"] == sha(rootpath) and tree["system_sha256"] == sha(systempath)
    assert tree["local_sha256"] == sha(localpath) and tree["constants_sha256"] == sha(constantspath)
    midpoint = [F(int(v), int(root["Qx"])) for v in root["xnum"]]
    eps = F(1, 10**80)
    anchors = [[(midpoint[2*(i-1)+axis]-eps, midpoint[2*(i-1)+axis]+eps)
                for axis in (0, 1)] for i in range(1, B)]
    print("N23 fresh core whole-angle replay started; actual nodes", len(tree["nodes"]), flush=True)
    result = exact.verify(B, coreN, masks, tree["nodes"], constants,
                          local=local(anchors, F(freshlocal["anchor_radius"])))
    assert result["verified"] and result["nodes"] == 30653
    assert result["counts"] == {"SPLIT": 15326, "DUAL": 15040, "LOCAL": 287}
    publish(output / "FRESH-ANGLE-REPLAY.json", {
        **result, "N": 23, "B": B, "tree_sha256": sha(treepath),
        "fresh_root_report_sha256": sha(output / "root-verified.json"),
        "fresh_local_report_sha256": sha(output / "FRESH-LOCAL-ISOLATION.json"),
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    for path, expected in frozen.items():
        assert sha(path) == expected
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "isolated-N23-same-root-upper-local-and-entire-core-domain-replay-v1",
        "N": 23, "B": B, "core_centers": coreN, "core_faces": masks,
        "root_interval_certificate_freshly_recomputed": True,
        "same_root_entire_disk_upper_freshly_recomputed": True,
        "all_local_exact_principal_minors_and_perturbation_gap_recomputed": True,
        "all_30653_core_angle_nodes_freshly_replayed": True,
        "local_leaves_require_the_fresh_root_and_local_proofs_not_report_flags_alone": True,
        "whole_core_lower_bound_is_nonstrict_same_root_not_strict_upper_exclusion": True,
        "no_actual_residual_type_claimed_to_contain_core_yet": True,
        "root_sha256": sha(rootpath), "system_sha256": sha(systempath),
        "tree_sha256": sha(treepath), "constants_sha256": sha(constantspath),
        "fresh_root_report_sha256": sha(output / "root-verified.json"),
        "fresh_upper_report_sha256": sha(output / "upper-verified.json"),
        "fresh_local_report_sha256": sha(output / "FRESH-LOCAL-ISOLATION.json"),
        "fresh_angle_report_sha256": sha(output / "FRESH-ANGLE-REPLAY.json"),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "exact_checker_sha256": sha(HIGH / "exact_graph.py"),
        "global_optimality_proved": False,
    })
    print("N23 core root, same-root upper, local isolation and entire-angle proof freshly accepted;",
          "no general-type or global payment", flush=True)


if __name__ == "__main__":
    main()
