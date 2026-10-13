"""Fresh N24 exact root, whole-disk upper, local isolation and core-angle replay.

The isolated historical assets and original routines are never overwritten.
This is a specified nonstrict core theorem, not a global topology payment.
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
    gamma, lam, nu, radius = 300, F(1, 5000), F(1, 100), F(1, 20)
    g, b, edges = data["G"], data["B"], data["edges"]
    assert (data["N"], b, g, data["D"]) == (24, 15, 114, 219)
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
    da = 4*(isqrt(4*m+2*(b-1))+1)*eps
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
        assert pivot > 0, ("non-positive N24 isolation pivot", k)
        hashes.append(hashlib.sha256(
            pivot.to_bytes((pivot.bit_length()+7)//8, "big")).hexdigest())
        for i in range(k+1, g):
            for j in range(i, g):
                value, remainder = divmod(pivot*h[i][j]-h[i][k]*h[k][j], previous)
                assert not remainder
                h[i][j] = h[j][i] = value
        previous = pivot
        if (k+1) % 20 == 0:
            print("N24 fresh exact isolation pivots", k+1, "/", g, flush=True)
    gap = lam-2*gamma*nu**2*radius**2
    assert gap > 0
    return {
        "verified": True, "N": 24,
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
    inputs, assets, output = (
        getattr(args, name).resolve() for name in ("inputs", "assets", "output"))
    assert all(path.is_relative_to(ROOT) for path in (inputs, assets, output))
    assert not output.exists()
    recovered = read(assets / "VERIFIED.json")
    assert recovered["verified"] and recovered["schema"] == "isolated-N24-core-exact-archive-assets-v1"
    assert recovered["source_sha256"] == sha(ROOT / "recover_n24_core_prerequisites.py")
    frozen = dict(recovered["frozen_files"])
    for path, digest in frozen.items():
        assert sha(path) == digest
    for path, binding in recovered["archive_bindings"].items():
        assert sha(path) == binding["archive_sha256"]
    folder = inputs / "n24"
    systempath, rootpath = folder / "core-system.json", folder / "core-root.json"
    localpath, treepath = assets / "local-isolation-certificate.json", assets / "core-angle-tree.json.gz"
    constantspath = SYN / "evidence/core-reduction/constants/n24.json"
    data, root, oldlocal, constants = map(read, (systempath, rootpath, localpath, constantspath))
    assert (data["N"], data["B"], data["G"], data["D"]) == (24, 15, 114, 219)
    assert root["system_sha256"] == sha(systempath)
    assert oldlocal["root_sha256"] == sha(rootpath)
    assert constants["verified"] and constants["N"] == 24
    assert F(constants["radius_upper"]) == F(61325412542131, 250000000000000)
    rootroutine, localroutine = SYN / "algebraic_roots.py", SYN / "local_certificates.py"
    for path in (Path(__file__), assets / "VERIFIED.json", inputs / "VERIFIED.json",
                 systempath, rootpath, folder / "candidate-numeric.json",
                 rootroutine, localroutine, SYN.parent / "n21-global/root_certificate.py",
                 SYN.parent / "n13-global/independent_checks.py",
                 localpath, treepath, constantspath, HIGH / "replay_candidate.py",
                 HIGH / "exact_graph.py", Path(exact.kernel.__file__)):
        frozen[str(path.resolve())] = sha(path)
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": 24, "B": 15, "explicit_original_root_upper_input_directory": str(inputs),
        "explicit_isolated_historical_tree_local_directory": str(assets),
        "N24_specific_radius_local_parameters_and_core_used": True,
        "original_root_upper_routines_not_rewritten": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    spec = importlib.util.spec_from_file_location("explicit_isolated_n24_root_upper", rootroutine)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.EV = inputs
    freshdata, z, rho = module.verify(24, output)
    assert freshdata == data
    assert read(output / "root-verified.json") == read(assets / "root-verified.json")
    module.upper(24, freshdata, z, rho, output)
    assert read(output / "upper-verified.json") == read(assets / "upper-verified.json")
    freshlocal = isolation(data, root)
    freshlocal["root_sha256"] = sha(rootpath)
    for key, value in freshlocal.items():
        assert oldlocal[key] == value, ("N24 historical local theorem replay differs", key)
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
    assert (tree["N"], tree["B"], tree["core_centers"], tree["faces"]) == (24, B, coreN, masks)
    assert tree["root_sha256"] == sha(rootpath) and tree["system_sha256"] == sha(systempath)
    assert tree["local_sha256"] == sha(localpath) and tree["constants_sha256"] == sha(constantspath)
    midpoint = [F(int(v), int(root["Qx"])) for v in root["xnum"]]
    eps = F(1, 10**80)
    anchors = [[(midpoint[2*(i-1)+axis]-eps, midpoint[2*(i-1)+axis]+eps)
                for axis in (0, 1)] for i in range(1, B)]
    print("N24 fresh entire-core angle replay started:", len(tree["nodes"]), "nodes", flush=True)
    result = exact.verify(
        B, coreN, masks, tree["nodes"], constants,
        local=local(anchors, F(freshlocal["anchor_radius"])))
    assert result["verified"] and result["nodes"] == 69215
    assert result["counts"] == {"SPLIT": 34607, "DUAL": 34129, "LOCAL": 479}
    publish(output / "FRESH-ANGLE-REPLAY.json", {
        **result, "N": 24, "B": B, "tree_sha256": sha(treepath),
        "fresh_root_report_sha256": sha(output / "root-verified.json"),
        "fresh_local_report_sha256": sha(output / "FRESH-LOCAL-ISOLATION.json"),
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    for path, digest in frozen.items():
        assert sha(path) == digest
    for path, binding in recovered["archive_bindings"].items():
        assert sha(path) == binding["archive_sha256"]
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "isolated-N24-same-root-upper-local-and-entire-core-replay-v1",
        "N": 24, "B": B, "core_centers": coreN, "core_faces": masks,
        "exact_root_interval_and_same_root_entire_disk_upper_freshly_recomputed": True,
        "all_114_local_principal_minors_and_perturbation_gap_freshly_recomputed": True,
        "all_69215_core_angle_nodes_freshly_mathematically_replayed": True,
        "LOCAL_leaves_require_actual_fresh_root_and_isolation_not_historical_flags": True,
        "specified_core_lower_bound_nonstrict_same_root_not_strict_upper_exclusion": True,
        "no_arbitrary_competitor_type_claimed_to_contain_this_core": True,
        "root_sha256": sha(rootpath), "system_sha256": sha(systempath),
        "tree_sha256": sha(treepath), "constants_sha256": sha(constantspath),
        "fresh_root_report_sha256": sha(output / "root-verified.json"),
        "fresh_upper_report_sha256": sha(output / "upper-verified.json"),
        "fresh_local_report_sha256": sha(output / "FRESH-LOCAL-ISOLATION.json"),
        "fresh_angle_report_sha256": sha(output / "FRESH-ANGLE-REPLAY.json"),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "exact_checker_sha256": sha(HIGH / "exact_graph.py"),
        "complete_competitor_families_cover_reduction_and_global_assembly_still_owed": True,
        "global_optimality_proved": False,
    })
    print("N24 specified core root, entire-disk upper, local isolation and whole-angle theorem accepted",
          "; no complete competitor or global payment", flush=True)


if __name__ == "__main__":
    main()
