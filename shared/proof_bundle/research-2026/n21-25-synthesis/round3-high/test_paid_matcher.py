"""Whole-library map regression and kernel-derivation gates, not a target proof."""
from pathlib import Path
import argparse
import json
import random
import subprocess
from audit_streamed_hierarchy import check_map
from stream_catalog import Catalog, sha, no_duplicate_keys
from paid_residual import PaidResidualCatalog

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def check_derivation():
    old = (ROOT / "peel_degree.cpp").read_text(encoding="utf8")
    controls = read(ROOT / "evidence/degree-pruning-regressions-resume1/VERIFIED.json")
    assert controls["verified"] and controls["source_sha256"] == sha(ROOT / "peel_degree.cpp")
    changes = [
        ("void visit(State const&s,vector<Region> pending){",
         '#include "paid_matcher.inc"\n\nvoid visit(State const&s,vector<Region> pending){'),
        ('<<" survivors="<<survivors.size()',
         '<<" residual="<<survivors.size()<<" proof_prunes="<<proof_prunes'),
        ("  prunes++;return;\n }\n if(pending.empty()){",
         "  prunes++;return;\n }\n if(already_paid(s))return;\n if(pending.empty()){"),
        ('if(argc!=10)throw runtime_error("usage: peel N B output scale cap2 cap4 cap6 node-limit mode(dfs|audit|noscreen|audit-noscreen)");',
         'if(argc!=11)throw runtime_error("usage: paid-peel N B output scale cap2 cap4 cap6 node-limit mode paid-table-or-minus");'),
        ('faces_needed=2*n-b-2;if(faces_needed>MAXF)throw runtime_error("face bitset bound");',
         'faces_needed=2*n-b-2;if(faces_needed>MAXF)throw runtime_error("face bitset bound");\n load_obstacles(argv[10]);'),
        ('f<<"{\\"complete\\":true,\\"N\\":"',
         'f<<"{\\"complete\\":false,\\"residual_complete\\":true,\\"schema\\":\\"paid-peeling-residual-v1\\",\\"N\\":"'),
        ('<<survivors.size()<<",\\"survivors\\":[";',
         '<<survivors.size();\n write_paid_summary(f);\n f<<",\\"survivors\\":[";'),
        ('cerr<<"COMPLETE B="<<b<<" calls="<<calls<<" orbits="<<survivors.size()<<"\\n";',
         'cerr<<"RESIDUAL COMPLETE B="<<b<<" calls="<<calls<<" orbits="<<survivors.size()<<" proof_prunes="<<proof_prunes<<"\\n";'),
    ]
    for before, after in changes:
        assert old.count(before) == 1, ("unexpected frozen kernel", before)
        old = old.replace(before, after, 1)
    assert old == (ROOT / "peel_paid_kernel.inc").read_text(encoding="utf8"), "unreviewed kernel changes"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    assert not args.output.is_absolute() and args.output.as_posix().isascii()
    args.output.mkdir(parents=True)
    check_derivation()
    librarydir = ROOT / "evidence/n22-portable-strict-obstacles-resume1"
    librarypath, tablepath = librarydir / "LIBRARY.json", librarydir / "OBSTACLES.tsv"
    library = read(librarypath)
    assert library["verified"] and library["all_library_trees_fresh_exact_replayed"]
    assert library["pattern_table_sha256"] == sha(tablepath)
    assert library["obstacle_count"] == len(library["obstacles"]) == 8671
    # All inputs of the fresh mathematical library acceptance remain unchanged.
    workspace = ROOT.parents[2]
    for relative, expected in library["files"].items():
        assert sha(workspace / relative) == expected, ("changed obstacle payment", relative)
    rng = random.Random(232425)
    positive = []
    rejected = []
    returned_orientations = set()
    for B in (13, 14, 15):
        patterns = [row for row in library["obstacles"] if row["B"] == B]
        requests = []
        for pattern in patterns:
            for variant in range(3):
                sign, shift = ((1, 0), (-1, B//2), (1, B-2))[variant]
                interior = list(range(B, 25))
                if variant:
                    rng.shuffle(interior)
                center = [(shift+sign*j) % B for j in range(B)]
                center += interior[:pattern["centers"]-B]
                assert len(set(center)) == len(center)
                faces = sorted(sum(1 << center[v] for v in range(pattern["centers"]) if mask >> v & 1)
                               for mask in pattern["faces"])
                requests.append((pattern["id"], faces))
        for pattern in patterns[:3]:
            # Every actual library pattern uses all boundary vertices.
            faces = [mask for mask in pattern["faces"] if not mask & 1]
            assert faces
            requests.append((-1, faces))
        requestpath = args.output / f"B{B}-requests.tsv"
        resultpath = args.output / f"B{B}-maps.json"
        with requestpath.open("x", encoding="ascii") as stream:
            for index, (_, faces) in enumerate(requests):
                stream.write("\t".join(map(str, [index, len(faces), *faces]))+"\n")
        subprocess.run([str(ROOT / "peel_paid.exe"), "match", "25", str(B),
                        str(tablepath.relative_to(ROOT)), str(requestpath), str(resultpath)],
                       cwd=ROOT, check=True)
        result = read(resultpath)
        assert len(result["matches"]) == len(requests)
        byid = {row["id"]: row for row in patterns}
        for index, (answer, (expected, faces)) in enumerate(zip(result["matches"], requests, strict=True)):
            assert answer["request"] == index and answer["obstacle"] == expected
            if expected < 0:
                rejected.append(f"B{B}-missing-boundary-pattern-{index}")
                continue
            pattern = byid[expected]
            mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
            check_map(25, B, pattern, mapping, set(faces), 2)
            returned_orientations.add(mapping["orientation"])
        positive.append({"B": B, "patterns": len(patterns), "all_transformed_maps_checked": 3*len(patterns),
                         "requests_sha256": sha(requestpath), "maps_sha256": sha(resultpath)})
        print("All portable patterns native/Python map regression PASS:", B, 3*len(patterns), flush=True)
    assert returned_orientations == {-1, 1}
    # Malformed tables and requests must not publish a matching result.
    original = library["obstacles"][0]
    normal = original["faces"]
    badlines = [
        "0\t1\t3\n", # not a triangle
        "0\t2\t"+str(normal[0])+"\t"+str(normal[0])+"\n",
        "1\t"+str(len(normal))+"\t"+"\t".join(map(str, normal))+"\n",
        "0\t"+str(len(normal))+"\t"+"\t".join(map(str, normal))+"\textra\n",
    ]
    for index, line in enumerate(badlines):
        req = args.output / f"invalid-request-{index}.tsv"
        out = args.output / f"invalid-result-{index}.json"
        req.write_text(line, encoding="ascii")
        result = subprocess.run([str(ROOT / "peel_paid.exe"), "match", "25", "13",
                                 str(tablepath.relative_to(ROOT)), str(req), str(out)],
                                cwd=ROOT, capture_output=True)
        assert result.returncode != 0 and not out.exists()
        rejected.append(f"malformed-request-{index}")
    # Small complete no-payment searches exactly match the old degree kernel.
    comparisons = []
    for B, I in ((3, 0), (3, 1), (3, 4), (6, 0), (6, 2), (8, 1)):
        N = B+I
        for mode in ("noscreen", "audit-noscreen"):
            reference = args.output / f"N{N}-B{B}-{mode}-reference.json"
            residual = args.output / f"N{N}-B{B}-{mode}-residual.json"
            params = [str(N), str(B), "10000000", "815002", "1690622", "2746810", "0", mode]
            subprocess.run([str(ROOT / "peel_degree.exe"), *params[:2], str(reference), *params[2:]],
                           cwd=ROOT, check=True, stderr=subprocess.DEVNULL)
            subprocess.run([str(ROOT / "peel_paid.exe"), *params[:2], str(residual), *params[2:], "-"],
                           cwd=ROOT, check=True, stderr=subprocess.DEVNULL)
            old = read(reference)
            new = PaidResidualCatalog(residual)
            rows = [row for _, row in new.rows()]
            assert new.finished and rows == old["survivors"]
            assert new.header["proof_prunes"] == 0
            try:
                Catalog(residual)
            except AssertionError:
                rejected.append(f"N{N}-B{B}-{mode}-residual-not-full")
            else:
                raise AssertionError("residual improperly accepted as a full necessary catalogue")
            comparisons.append({"N": N, "B": B, "mode": mode, "orbits": len(rows),
                                "reference_sha256": sha(reference), "residual_sha256": sha(residual)})
    limited = args.output / "node-limit-must-not-publish.json"
    result = subprocess.run([str(ROOT / "peel_paid.exe"), "23", "13", str(limited),
                             "10000000", "804156", "1666328", "2698800", "1", "dfs",
                             str(tablepath.relative_to(ROOT))], cwd=ROOT, capture_output=True)
    assert result.returncode != 0 and not limited.exists()
    rejected.append("node-limit-before-residual-publication")
    report = {"verified": True, "all_library_patterns_matched": True,
              "positive_transformed_maps": 3*8671, "map_tests": positive,
              "all_no_payment_whole_sets_match": comparisons,
              "negative_controls_rejected": rejected,
              "original_degree_kernel_preserved": True, "kernel_derivation_verified": True,
              "library_sha256": sha(librarypath), "table_sha256": sha(tablepath),
              "source_sha256": sha(Path(__file__)),
              "native_sources_sha256": {name: sha(ROOT / name) for name in
                  ("peel_paid.cpp", "peel_paid_kernel.inc", "paid_matcher.inc", "peel_degree.cpp")},
              "binary_sha256": sha(ROOT / "peel_paid.exe"),
              "residual_reader_sha256": sha(ROOT / "paid_residual.py"),
              "global_optimality_proved": False,
              "scope": "kernel derivation, whole obstacle map tests and toy complete search controls"}
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Paid-kernel controls PASS:", 3*8671, "explicit maps,", len(comparisons),
          "whole-set controls,", len(rejected), "negative controls", flush=True)


if __name__ == "__main__":
    main()
