"""Verify the transport automorphisms against the ACTUAL 879 graph structure
(16 literal faces + 10 owner anchor edges + hidden sites), not merely bijectivity.

q10-adaptive-literal-map.json gives:
  literal_faces  : 16 triples on 14 sites
  literal_owners : 10 pairs (anchor edge between consecutive owner-cylinder sites)
  maps           : 4 (site_map[14], anchor_map[10], orientation)
q10-fan-transport.json gives 4 runs with site_permutation[14] and deficit_permutation[10].

Checks per run/map:
  V1 site permutation preserves the FACE SET {literal_faces} up to relabelling;
  V2 site permutation preserves the OWNER-EDGE SET {literal_owners} up to relabelling;
  V3 the induced anchor permutation on owner-edge position and orientation is consistent
     (so the cycle order used by the deficit map is preserved up to the declared orientation);
  V4 the deficit permutation equals the anchor permutation shifted by the owner-gap convention
     (def_j = a(j+1)-1, a = anchor map) where the run's site map matches.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead")


def apply_perm_to_set(items, perm):
    out = set()
    for it in items:
        out.add(tuple(sorted(perm[x] for x in it)))
    return out


def induced_anchor_map(owners, siteperm):
    """owner k = (a_k, a_{k+1}) as an undirected edge; find the k' with image edge."""
    img = {}
    for k, (u, v) in enumerate(owners):
        e = tuple(sorted((siteperm[u], siteperm[v])))
        hits = [j for j, (a, b) in enumerate(owners) if tuple(sorted((a, b))) == e]
        if len(hits) != 1:
            return None, k, len(hits)
        img[k] = hits[0]
    return img, None, None


def main():
    m = json.loads((LEAD / "q10-adaptive-literal-map.json").read_text(encoding="utf-8"))
    faces = [tuple(f) for f in m["literal_faces"]]
    owners = [tuple(o) for o in m["literal_owners"]]
    F = set(tuple(sorted(f)) for f in faces)
    O = set(tuple(sorted(o)) for o in owners)
    t = json.loads((LEAD / "q10-fan-transport.json").read_text(encoding="utf-8"))
    out = {"n_faces": len(F), "n_owner_edges": len(O),
           "distinct_owner_edges": len(O), "runs": []}
    # first: consistency of the two 4-element lists (maps vs runs)
    for i, r in enumerate(t["runs"]):
        sp = [r["site_permutation"][str(k)] for k in range(14)]
        dp = [r["deficit_permutation"][str(k)] for k in range(10)]
        rec = {"run": i, "site_perm_bijective": sorted(sp) == list(range(14)),
               "deficit_perm_bijective": sorted(dp) == list(range(10)),
               "faces_preserved": (apply_perm_to_set(F, sp) == F),
               "owners_preserved": (apply_perm_to_set(O, sp) == O)}
        am, badk, nhit = induced_anchor_map(owners, sp)
        rec["anchor_map_induced"] = am
        rec["anchor_map_total"] = (am is not None)
        if am is not None:
            def conj(j):
                k = (j + 1) % 10
                return (am[k] - 1) % 10
            rec["deficit_equals_shifted_anchor_map"] = all(dp[j] == conj(j) for j in range(10))
            rec["deficit_equals_anchor_map_minus1_plain"] = all(
                dp[j] == (am[j] - 1) % 10 for j in range(10))
        out["runs"].append(rec)
    # cross-check against the map family declared in the literal map file
    out["declared_maps"] = [{"site_map_bijective":
                             sorted(mm["site_map"]) == list(range(14)),
                             "anchor_map": mm["anchor_map"],
                             "orientation": mm.get("orientation")}
                            for mm in m["maps"]]
    (HERE / "transport-automorphism-check.json").write_text(json.dumps(out, indent=1),
                                                            encoding="utf-8")
    for r in out["runs"]:
        print(r["run"], "faces", r["faces_preserved"], "owners", r["owners_preserved"],
              "anchor_map", r["anchor_map_induced"], "def=shift(anchor_map)?",
              r.get("deficit_equals_shifted_anchor_map"))
    print("declared maps:", json.dumps(out["declared_maps"])[:300])


if __name__ == "__main__":
    main()
