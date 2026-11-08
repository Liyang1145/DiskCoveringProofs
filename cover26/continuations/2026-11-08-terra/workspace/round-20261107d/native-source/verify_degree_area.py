"""Pure integer/Fraction Voronoi polygon/arc area exclusion certificates."""

import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from pathlib import Path


U = F(234701, 10**6)
CAP = F(754112, 10**7)
SLOPE = F(-23, 4)
COEFFICIENT_SCALE = 10**12
TRIG_SHA = "836517e7597085151d68bd663d9906340ed0f4b64c3042e8265645718f4d599b"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_trig(folder=None):
    path = Path(folder or Path(__file__).parent) / "exact_arcs.py"
    if not path.exists():
        from new_upper_scope import ARCS, local_path
        path = local_path(str(ARCS))
    if sha(path) != TRIG_SHA:
        raise ValueError("unbound exact trigonometric arithmetic")
    spec = importlib.util.spec_from_file_location("bound_degree_area_arcs", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module, path


def parameter_gate(cert):
    if not (cert["N"] == 26 and F(cert["radius_threshold"]) == U
            and F(cert["boundary_gap_cap_turns"]) == CAP
            and F(cert["dual_slope"]) == SLOPE
            and cert["coefficient_scale"] == COEFFICIENT_SCALE
            and cert["trig_sha256"] == TRIG_SHA
            and cert["full_catalog_complete"] is False
            and cert["global_optimality_proved"] is False):
        raise ValueError("wrong area-certificate scope or constants")
    n, q = cert["bins"], cert["beta_grid_Q"]
    if type(n) is not int or n != 8192 or type(q) is not int or q != 2**24:
        raise ValueError("wrong rational partition")
    if len(cert["beta_lower_numerators"]) != n:
        raise ValueError("incomplete beta lower-bound table")
    if any(type(k) is not int or not 0 <= k <= q for k in cert["beta_lower_numerators"]):
        raise ValueError("invalid beta grid value")
    for key in ("boundary_intercept_upper_integers", "interior_area_upper_integers"):
        if len(cert[key]) != 24 or any(type(k) is not int for k in cert[key]):
            raise ValueError("invalid coefficient table")


def sin_iv(arcs, turns):
    lo, hi = arcs.sincos_turn(turns)[1]
    return F(lo, arcs.SCALE), F(hi, arcs.SCALE)


def beta_gate(arcs, numerator, q, lower_sine):
    beta = F(numerator, 4 * q)
    if sin_iv(arcs, beta)[1] > lower_sine / U:
        raise ValueError("proposed beta is not a certified lower angle")
    return beta


def derive_tables(cert, arcs, progress=False):
    """Reconstruct every bin bound, not a sampling maximum."""
    n, q = cert["bins"], cert["beta_grid_Q"]
    regular = {d: U**2 * F(d + 1, 2) * sin_iv(arcs, F(1, d + 1))[1]
               for d in range(2, 26)}
    maxima = {d: None for d in range(2, 26)}
    max_bins = {}
    infeasible = 0
    for i in range(n):
        lo, hi = CAP * i / n, CAP * (i + 1) / n
        sine_lower = sin_iv(arcs, lo / 2)[0]
        if sine_lower > U:
            infeasible += 1
            continue
        beta = None
        numerator = cert["beta_lower_numerators"][i]
        if 2 * sine_lower > U:
            beta = beta_gate(arcs, numerator, q, sine_lower)
        elif numerator:
            raise ValueError("unused beta entry must be zero")
        sin_gap_lower = sin_iv(arcs, lo)[0]
        for d in range(2, 26):
            polygon = regular[d]
            if beta is not None and beta >= F(1, 2 * (d + 1)):
                polygon = U**2 / 2 * (
                    sin_iv(arcs, 2 * beta)[1]
                    + d * sin_iv(arcs, (1 - 2 * beta) / d)[1])
            # P_d(s) is bounded using the left endpoint; sine(2*pi*s)
            # is increasing on this entire domain. -SLOPE*s is increasing.
            bound = polygon - sin_gap_lower / 2 - SLOPE * hi
            if maxima[d] is None or bound > maxima[d]:
                maxima[d], max_bins[d] = bound, i
        if progress and (i + 1) % 1024 == 0:
            print(json.dumps({"exact_area_bins_checked": i + 1, "of": n}), flush=True)
    interior = {d: U**2 * F(d, 2) * sin_iv(arcs, F(1, d))[1]
                for d in range(2, 26)}
    return maxima, interior, max_bins, infeasible


def table_claim_gate(cert, maxima, interior):
    for index, d in enumerate(range(2, 26)):
        if F(cert["boundary_intercept_upper_integers"][index], COEFFICIENT_SCALE) < maxima[d]:
            raise ValueError("boundary area coefficient too small")
        if F(cert["interior_area_upper_integers"][index], COEFFICIENT_SCALE) < interior[d]:
            raise ValueError("interior area coefficient too small")


def degrees(b, faces):
    if len(faces) != 50 - b or len(set(faces)) != len(faces):
        raise ValueError("invalid center-face count")
    adjacency = [set() for _ in range(26)]
    edges = Counter()
    links = [dict() for _ in range(26)]
    for f in faces:
        if type(f) is not int or not 0 < f < 2**26 or f.bit_count() != 3:
            raise ValueError("invalid face mask")
        v = [i for i in range(26) if f >> i & 1]
        for i in v:
            adjacency[i].update(j for j in v if j != i)
            a, c = [j for j in v if j != i]
            links[i].setdefault(a, set()).add(c)
            links[i].setdefault(c, set()).add(a)
        for i in range(3):
            for j in range(i + 1, 3):
                edges[v[i], v[j]] += 1
    boundary = {tuple(sorted((i, (i + 1) % b))) for i in range(b)}
    if not boundary <= set(edges) or any(count != (1 if edge in boundary else 2)
                                        for edge, count in edges.items()):
        raise ValueError("invalid disk edge incidence")
    if 26 - len(edges) + len(faces) != 1:
        raise ValueError("invalid Euler data")
    for i, link in enumerate(links):
        if not link:
            raise ValueError("unused vertex")
        expected = {(i - 1) % b, (i + 1) % b} if i < b else set()
        if {j for j, row in link.items() if len(row) == 1} != expected:
            raise ValueError("wrong link endpoints")
        if any(len(row) not in (1, 2) for row in link.values()):
            raise ValueError("nonmanifold vertex")
        seen, pending = set(), [next(iter(link))]
        while pending:
            j = pending.pop()
            if j not in seen:
                seen.add(j)
                pending.extend(link[j] - seen)
        if seen != set(link):
            raise ValueError("disconnected vertex link")
    counts_b = Counter(len(adjacency[i]) for i in range(b))
    counts_i = Counter(len(adjacency[i]) for i in range(b, 26))
    if min(counts_b) < 2 or min(counts_i) < 3:
        raise ValueError("invalid valence")
    return (tuple(counts_b[d] for d in range(2, 26)),
            tuple(counts_i[d] for d in range(2, 26)))


def source_gate(folder, cert):
    source_path = folder / "SOURCE.json"
    if cert["source_sha256"] != sha(source_path):
        raise ValueError("changed source-catalog inventory")
    source = json.loads(source_path.read_text(encoding="utf-8"))
    if source["full_catalog_complete"] or source["global_optimality_proved"]:
        raise ValueError("source catalogs falsely claim completion")
    graphs, paths = set(), [source_path]
    for entry in source["catalogs"]:
        path = folder / entry["filename"]
        if path.parent != folder or sha(path) != entry["sha256"]:
            raise ValueError("changed source catalog")
        paths.append(path)
        data = json.loads(path.read_text(encoding="utf-8"))
        b = entry["B"]
        if not (b in (14, 15, 16, 17) and data["N"] == 26 and data["B"] == b
                and data["complete"] and not data["family_complete"]
                and data["operation"] == "solve" and data["origin_screen"] and data["screen"]
                and data["scale"] == 10**7 and data["caps"] == [754112, 1555305, 2486507, 3880649]
                and not data["global_optimality_proved"] and not data["geometric_reduction_proved"]):
            raise ValueError("wrong selected-catalog scope")
        for graph in data["survivors"]:
            graphs.add((b, tuple(sorted(graph["faces"]))))
    if len(graphs) != source["selected_distinct_graphs"] or len(paths) != 1 + source["selected_closed_subtrees"]:
        raise ValueError("selected graph union not complete")
    return sorted(graphs), paths


def ledger_for(graphs, cert):
    profiles = {}
    graph_rows = []
    for b, faces in graphs:
        p = degrees(b, faces)
        if p not in profiles:
            boundary, interior = p
            dual = sum(n * c for n, c in zip(boundary, cert["boundary_intercept_upper_integers"]))
            dual += sum(n * c for n, c in zip(interior, cert["interior_area_upper_integers"]))
            dual += int(SLOPE * COEFFICIENT_SCALE)
            profiles[p] = {"profile_id": len(profiles),
                           "boundary_degree_counts_d2_to_d25": list(boundary),
                           "interior_degree_counts_d2_to_d25": list(interior),
                           "area_dual_upper_scaled_integer": dual,
                           "strictly_excluded_as_cover_transport_type": dual < 0,
                           "selected_graph_count": 0}
        row = profiles[p]
        row["selected_graph_count"] += 1
        graph_rows.append([b, list(faces), row["profile_id"]])
    ledger = sorted(profiles.values(), key=lambda row: row["profile_id"])
    excluded = [row for row in ledger if row["strictly_excluded_as_cover_transport_type"]]
    result = {
        "profiles": len(ledger), "selected_graphs": len(graphs),
        "strictly_excluded_profiles": len(excluded),
        "strictly_excluded_graphs": sum(row["selected_graph_count"] for row in excluded),
        "still_unresolved_graphs": sum(row["selected_graph_count"] for row in ledger
                                       if not row["strictly_excluded_as_cover_transport_type"]),
        "smallest_strict_area_margin": (
            str(F(min(-row["area_dual_upper_scaled_integer"] for row in excluded),
                  COEFFICIENT_SCALE)) if excluded else None),
    }
    return ledger, graph_rows, result


def publish_or_match(path, data):
    if path.exists():
        if json.loads(path.read_text(encoding="utf-8")) != data:
            raise ValueError("frozen ledger differs from exact replay")
    else:
        path.write_text(json.dumps(data, separators=(",", ":")) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    cert_path = args.input / "CERTIFICATE.json"
    cert = json.loads(cert_path.read_text(encoding="utf-8"))
    parameter_gate(cert)
    arcs, trig_path = load_trig(args.input)
    maxima, interior, max_bins, infeasible = derive_tables(cert, arcs, progress=True)
    table_claim_gate(cert, maxima, interior)
    graphs, source_paths = source_gate(args.input, cert)
    ledger, graph_rows, result = ledger_for(graphs, cert)
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("bad area input accepted: " + label)

    wrong = deepcopy(cert)
    wrong["radius_threshold"] = "1/4"
    reject("changed-radius-threshold", lambda: parameter_gate(wrong))
    wrong = deepcopy(cert)
    wrong["beta_lower_numerators"].pop()
    reject("missing-interval-bin", lambda: parameter_gate(wrong))
    wrong = deepcopy(cert)
    wrong["boundary_intercept_upper_integers"][1] = 0
    reject("understated-boundary-area", lambda: table_claim_gate(wrong, maxima, interior))
    wrong = deepcopy(cert)
    wrong["interior_area_upper_integers"][1] = 0
    reject("understated-interior-area", lambda: table_claim_gate(wrong, maxima, interior))
    reject("false-beta-lower-bound", lambda: beta_gate(arcs, cert["beta_grid_Q"],
                                                     cert["beta_grid_Q"], F(3, 4) * U))
    wrong = deepcopy(cert)
    wrong["source_sha256"] = "0" * 64
    reject("changed-catalog-inventory", lambda: source_gate(args.input, wrong))
    wrong = deepcopy(cert)
    wrong["global_optimality_proved"] = True
    reject("false-global-optimality", lambda: parameter_gate(wrong))
    profile_path, graph_path = args.input / "PROFILE-LEDGER.json", args.input / "GRAPH-LEDGER.json"
    publish_or_match(profile_path, ledger)
    publish_or_match(graph_path, graph_rows)
    files = source_paths + [cert_path, profile_path, graph_path, trig_path,
                            args.input / "verify_degree_area.py", args.input / "PROOF.md"]
    report = {
        "schema": "N26-Voronoi-degree-boundary-arc-strict-area-lower-v1",
        "verified": True, "all_continuous_gap_bins_checked": True,
        "rational_interval_bins": cert["bins"], "degree_range": [2, 25],
        "excluded_whole_bins_as_infeasible": infeasible,
        "dual_slope": str(SLOPE), "coefficient_scale": COEFFICIENT_SCALE,
        "maximizing_bound_bin_by_boundary_degree": max_bins, **result,
        "exclusion_scope": "Generic irredundant Voronoi transport types, including star-padding to 26 labels; not all weak rod realizations",
        "written_transport_and_area_lemmas_required": True,
        "formal_machine_geometry_proof": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False,
        "negative_controls_rejected": negatives,
        "files": {p.name: sha(p) for p in files},
        "executed_checker_sha256": sha(__file__),
    }
    if report["executed_checker_sha256"] != report["files"]["verify_degree_area.py"]:
        raise ValueError("executed and published checker differ")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in
                     ("files", "maximizing_bound_bin_by_boundary_degree")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
