"""Exact negative-cycle certificates from short rod paths and ordered anchors.

The discovery algorithm is not trusted. Each accepted cycle is rechecked as a
sum of individually justified difference inequalities with a negative total.
This certifies standalone graphs, not coverage of a complete topology family.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys
sys.path.insert(0, str(exact.kernel.ARCS))
import exact_arcs as arcs

assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def constants_gate(constants):
    assert constants["verified"] and constants["N"] == 25
    D, caps = constants["angle_scale"], constants["angle_caps"]
    U = F(constants["radius_upper"])
    assert D == 10**7 and len(caps) == 3 and 0 < caps[0]*2 < caps[1] < caps[2] < D//2
    for k, cap in enumerate(caps, 1):
        sine_lower = F(arcs.sincos_turn(F(cap, 2*D))[1][0], arcs.SCALE)
        assert sine_lower > k*U


def adjacency(B, centers, masks):
    exact.graph(B, centers, masks)
    adj = [set() for _ in range(centers)]
    for mask in masks:
        face = exact.kernel.bits(mask)
        for vertex in face:
            adj[vertex].update(set(face)-{vertex})
    return adj


def inequalities(B, centers, masks, constants):
    adj = adjacency(B, centers, masks)
    D, caps = constants["angle_scale"], constants["angle_caps"]
    A = caps[0]
    edges = []
    for i in range(B):
        j = (i+1) % B
        edges.append({"u": i, "v": j, "weight": A-(D if j == 0 else 0),
                      "kind": "consecutive-upper", "index": i})
        edges.append({"u": j, "v": i, "weight": D if j == 0 else 0,
                      "kind": "consecutive-lower", "index": i})
    for i in range(B):
        for j in range(i+1, B):
            chosen = None
            for start in (i, (i+1) % B):
                todo = [[start]]
                for path in todo:
                    if path[-1] in (j, (j+1) % B):
                        if chosen is None or len(path) < len(chosen):
                            chosen = path
                        break
                    if len(path) < 3:
                        todo.extend(path+[other] for other in sorted(adj[path[-1]]) if other not in path)
            if chosen is None:
                continue
            cap = caps[len(chosen)-1]
            k = j-i
            if min(k, B-k)*A <= cap:
                continue
            if k*A < D-cap:
                edges.append({"u": i, "v": j, "weight": cap, "kind": "short-path",
                              "i": i, "j": j, "path": chosen, "direction": 1})
            if (B-k)*A < D-cap:
                edges.append({"u": j, "v": i, "weight": cap-D, "kind": "short-path",
                              "i": i, "j": j, "path": chosen, "direction": -1})
    return edges


def find_cycle(B, edges):
    distance, predecessor = [0]*B, [None]*B
    changed = None
    for _ in range(B):
        changed = None
        for edge in edges:
            u, v, weight = edge["u"], edge["v"], edge["weight"]
            if distance[v] > distance[u]+weight:
                distance[v] = distance[u]+weight
                predecessor[v] = edge
                changed = v
        if changed is None:
            return None
    vertex = changed
    for _ in range(B):
        assert predecessor[vertex] is not None
        vertex = predecessor[vertex]["u"]
    end, backward = vertex, []
    while True:
        edge = predecessor[vertex]
        assert edge is not None
        backward.append(edge)
        vertex = edge["u"]
        if vertex == end:
            break
        assert len(backward) <= B
    return list(reversed(backward))


def verify_cycle(B, centers, masks, cycle, constants):
    """Check only each supplied implication and its contradictory exact sum."""
    adj = adjacency(B, centers, masks)
    D, caps = constants["angle_scale"], constants["angle_caps"]
    A = caps[0]
    assert type(cycle) is list and 1 <= len(cycle) <= B
    for index, edge in enumerate(cycle):
        assert type(edge["u"]) is int and type(edge["v"]) is int
        assert 0 <= edge["u"] < B and 0 <= edge["v"] < B
        assert type(edge["weight"]) is int
        assert edge["v"] == cycle[(index+1) % len(cycle)]["u"]
        if edge["kind"] in ("consecutive-upper", "consecutive-lower"):
            assert set(edge) == {"u", "v", "weight", "kind", "index"}
            i = edge["index"]
            assert type(i) is int and 0 <= i < B
            j = (i+1) % B
            expected = ((i, j, A-(D if j == 0 else 0)) if edge["kind"] == "consecutive-upper"
                        else (j, i, D if j == 0 else 0))
            assert (edge["u"], edge["v"], edge["weight"]) == expected
        else:
            assert edge["kind"] == "short-path"
            assert set(edge) == {"u", "v", "weight", "kind", "i", "j", "path", "direction"}
            i, j, path, sign = edge["i"], edge["j"], edge["path"], edge["direction"]
            assert type(i) is int and type(j) is int and 0 <= i < j < B
            assert type(path) is list and 1 <= len(path) <= 3
            assert all(type(v) is int and 0 <= v < centers for v in path)
            assert path[0] in (i, (i+1) % B) and path[-1] in (j, (j+1) % B)
            assert all(v in adj[u] for u, v in zip(path, path[1:]))
            cap = caps[len(path)-1]
            if sign == 1:
                assert (j-i)*A < D-cap
                assert (edge["u"], edge["v"], edge["weight"]) == (i, j, cap)
            else:
                assert sign == -1 and (B-j+i)*A < D-cap
                assert (edge["u"], edge["v"], edge["weight"]) == (j, i, cap-D)
    total = sum(edge["weight"] for edge in cycle)
    assert total < 0
    return {"verified": True, "cycle_length": len(cycle), "negative_integer_sum": total,
            "angle_scale": D, "scope": "standalone full-angle graph contradiction"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path)
    ap.add_argument("--B", type=int, choices=(14, 15, 16, 17))
    ap.add_argument("--replay", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    constpath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constpath)
    constants_gate(constants)
    if args.replay:
        certificate = read(args.replay)
        assert certificate["schema"] == "standalone-short-path-negative-cycles-v1"
        assert certificate["source_sha256"] == sha(Path(__file__))
        assert certificate["constants_sha256"] == sha(constpath)
        totals = Counter()
        for row in certificate["outcomes"]:
            totals[row["status"]] += 1
            if row["status"] == "excluded":
                assert verify_cycle(certificate["B"], row["centers"], row["faces"],
                                    row["cycle"], constants) == row["exact_cycle_check"]
        assert dict(totals) == certificate["totals"]
        report = {"verified": True, "certificate_sha256": sha(args.replay),
                  "constants_sha256": sha(constpath), "totals": dict(totals),
                  "all_cycles_individually_checked": True, "no_optimizer_imported": True,
                  "source_sha256": sha(Path(__file__)), "global_optimality_proved": False}
    else:
        assert args.library and args.B
        library = read(args.library)
        assert library["verified"]
        outcomes, totals = [], Counter()
        for obstacle in library["obstacles"]:
            if obstacle["B"] != args.B:
                continue
            centers, masks = obstacle["centers"], obstacle["faces"]
            cycle = find_cycle(args.B, inequalities(args.B, centers, masks, constants))
            row = {"source_obstacle": obstacle["id"], "centers": centers, "faces": masks,
                   "status": "pending" if cycle is None else "excluded"}
            if cycle is not None:
                row["cycle"] = cycle
                row["exact_cycle_check"] = verify_cycle(args.B, centers, masks, cycle, constants)
            totals[row["status"]] += 1
            outcomes.append(row)
        assert outcomes
        report = {"schema": "standalone-short-path-negative-cycles-v1", "N": 25, "B": args.B,
                  "source_library_sha256": sha(args.library), "constants_sha256": sha(constpath),
                  "outcomes": outcomes, "totals": dict(totals), "source_sha256": sha(Path(__file__)),
                  "complete_family_coverage": False, "global_optimality_proved": False}
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf8")
    print("Exact short-path negative-cycle results:", dict(totals),
          "; no complete-family claim", flush=True)


if __name__ == "__main__":
    main()
