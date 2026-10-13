"""Generate rational proposals; the published independent replay accepts them."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import WORK
from new_upper_scope import local_path
from run_new_scope_batch import audit
from verify_degree_area import (
    CAP, COEFFICIENT_SCALE, SLOPE, TRIG_SHA, U, derive_tables, load_trig, sha,
)


def ceil_integer(value):
    return -((-value.numerator) // value.denominator)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    arcs, trig_path = load_trig()
    bins, q = 8192, 2**24
    beta = []
    previous = 0
    for i in range(bins):
        x = CAP * i / bins
        lower = F(arcs.sincos_turn(x / 2)[1][0], arcs.SCALE)
        if lower > U or 2 * lower <= U:
            beta.append(0)
            continue
        lo, hi = previous, q
        while hi - lo > 1:
            mid = (lo + hi) // 2
            upper_sine = F(arcs.sincos_turn(F(mid, 4 * q))[1][1], arcs.SCALE)
            if upper_sine <= lower / U:
                lo = mid
            else:
                hi = mid
        beta.append(lo)
        previous = lo
        if (i + 1) % 1024 == 0:
            print(json.dumps({"beta_proposals": i + 1, "of": bins}), flush=True)
    cert = {
        "schema": "N26-degree-arc-area-rational-dual-certificate-v1",
        "N": 26, "radius_threshold": str(U), "boundary_gap_cap_turns": str(CAP),
        "dual_slope": str(SLOPE), "coefficient_scale": COEFFICIENT_SCALE,
        "trig_sha256": TRIG_SHA, "bins": bins, "beta_grid_Q": q,
        "beta_lower_numerators": beta,
        "full_catalog_complete": False, "global_optimality_proved": False}
    maxima, interior, _, _ = derive_tables(cert, arcs, progress=True)
    cert["boundary_intercept_upper_integers"] = [
        ceil_integer(maxima[d] * COEFFICIENT_SCALE) + 1 for d in range(2, 26)]
    cert["interior_area_upper_integers"] = [
        ceil_integer(interior[d] * COEFFICIENT_SCALE) + 1 for d in range(2, 26)]
    args.output.mkdir(parents=True)
    catalogs, original_files, graphs = [], {}, set()
    for b in (14, 15, 16, 17):
        report_path = WORK.parent / f"outputs/n26-new-B{b}-progress-v1.json"
        report = json.loads(report_path.read_text())
        checkpoint_path = local_path(report["latest_checkpoint"])
        if sha(checkpoint_path) != report["checkpoint_sha256"]:
            raise ValueError("changed selected progress checkpoint")
        manifest = json.loads(checkpoint_path.read_text())
        audit(manifest)
        original_files[str(report_path)] = sha(report_path)
        original_files[str(checkpoint_path)] = sha(checkpoint_path)
        for event in manifest["events"]:
            if event["kind"] != "closed":
                continue
            original = local_path(event["run"]["path"])
            if sha(original) != event["run"]["sha256"]:
                raise ValueError("changed completed subtree")
            filename = f"catalog-N26-B{b}-{len(catalogs):03d}.json"
            target = args.output / filename
            target.write_bytes(original.read_bytes())
            data = json.loads(target.read_text())
            graphs.update((b, tuple(sorted(g["faces"]))) for g in data["survivors"])
            catalogs.append({"filename": filename, "B": b, "sha256": sha(target),
                             "original_path": str(original), "prefix": data["prefix"]})
            original_files[str(original)] = sha(original)
    source = {"schema": "N26-selected-completed-subtree-catalogs-v1",
              "selected_closed_subtrees": len(catalogs), "selected_distinct_graphs": len(graphs),
              "catalogs": catalogs, "original_files": original_files,
              "full_catalog_complete": False, "global_optimality_proved": False}
    source_path = args.output / "SOURCE.json"
    source_path.write_text(json.dumps(source, indent=2) + "\n", encoding="utf-8")
    cert["source_sha256"] = sha(source_path)
    (args.output / "CERTIFICATE.json").write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
    for original, filename in (
        (trig_path, "exact_arcs.py"), (WORK / "verify_degree_area.py", "verify_degree_area.py"),
        (WORK / "n26-degree-area-proof.md", "PROOF.md")):
        (args.output / filename).write_bytes(original.read_bytes())
    (args.output / "BUILT.json").write_text(json.dumps({
        "verified": False, "builder_sha256": sha(__file__),
        "source_sha256": sha(source_path), "global_optimality_proved": False}, indent=2) + "\n")
    print(json.dumps({"built": True, "verified": False, "selected_graphs": len(graphs)}), flush=True)


if __name__ == "__main__":
    main()
