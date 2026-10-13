"""Independent integer-cycle acceptance with paths of at most eight rods."""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict, deque
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
import exact_graph as exact
from angle_obstructions import find_cycle
sys.path.insert(0, str(exact.kernel.ARCS))
import exact_arcs as arcs

assert __debug__
CAP8 = 4058615


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def constants_gate(constants, cap8=CAP8):
    assert constants["verified"] and constants["N"] == 25
    D, caps = constants["angle_scale"], constants["angle_caps"]+[cap8]
    U = F(constants["radius_upper"])
    assert U == F(239146311738101, 10**15) and D == 10**7
    assert 0 < 2*caps[0] < caps[1] < caps[2] < caps[3] < D//2
    margins = []
    for k, cap in enumerate(caps, 1):
        margin = F(arcs.sincos_turn(F(cap, 2*D))[1][0], arcs.SCALE)-k*U
        assert margin > 0
        margins.append(str(margin))
    return margins


def adjacency(B, centers, masks):
    assert type(B) is int and type(centers) is int and 3 <= B <= centers <= 25
    assert masks == sorted(set(masks))
    assert all(type(m) is int and 0 < m < 1 << centers and m.bit_count() == 3 for m in masks)
    adj = [set() for _ in range(centers)]
    for mask in masks:
        face = [v for v in range(centers) if mask >> v & 1]
        for v in face:
            adj[v].update(set(face)-{v})
    # Both center endpoints of a boundary edge have a common unit anchor.
    for i in range(B):
        j = (i+1) % B
        adj[i].add(j)
        adj[j].add(i)
    return adj


def inequalities(B, centers, masks, constants, cap8=CAP8):
    adj = adjacency(B, centers, masks)
    D, caps = constants["angle_scale"], constants["angle_caps"]+[cap8]
    A, edges = caps[0], []
    for i in range(B):
        j = (i+1) % B
        edges.append({"u": i, "v": j, "weight": A-(D if j == 0 else 0),
                      "kind": "consecutive-upper", "index": i})
        edges.append({"u": j, "v": i, "weight": D if j == 0 else 0,
                      "kind": "consecutive-lower", "index": i})
    for i in range(B):
        paths = {}
        queue = deque([[i], [(i+1) % B]])
        while queue:
            path = queue.popleft()
            end = path[-1]
            if end in paths:
                continue
            paths[end] = path
            if len(path) < 4:
                queue.extend(path+[v] for v in sorted(adj[end]) if v not in paths)
        for j in range(i+1, B):
            options = [paths[v] for v in (j, (j+1) % B) if v in paths]
            if not options:
                continue
            path = min(options, key=lambda p: (len(p), p))
            cap, k = caps[len(path)-1], j-i
            if min(k, B-k)*A <= cap:
                continue
            if k*A < D-cap:
                edges.append({"u": i, "v": j, "weight": cap, "kind": "short-path",
                              "i": i, "j": j, "path": path, "direction": 1})
            if (B-k)*A < D-cap:
                edges.append({"u": j, "v": i, "weight": cap-D, "kind": "short-path",
                              "i": i, "j": j, "path": path, "direction": -1})
    return edges


def verify_cycle(B, centers, masks, cycle, constants, cap8=CAP8):
    adj = adjacency(B, centers, masks)
    D, caps = constants["angle_scale"], constants["angle_caps"]+[cap8]
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
            assert type(path) is list and 1 <= len(path) <= 4
            assert all(type(v) is int and 0 <= v < centers for v in path)
            assert path[0] in (i, (i+1) % B) and path[-1] in (j, (j+1) % B)
            assert all(v in adj[u] for u, v in zip(path, path[1:]))
            cap = caps[len(path)-1]
            if sign == 1:
                assert (j-i)*A < D-cap
                expected = (i, j, cap)
            else:
                assert sign == -1 and (B-j+i)*A < D-cap
                expected = (j, i, cap-D)
            assert (edge["u"], edge["v"], edge["weight"]) == expected
    total = sum(edge["weight"] for edge in cycle)
    assert total < 0
    return {"verified": True, "cycle_length": len(cycle), "negative_integer_sum": total,
            "angle_scale": D, "cap8": cap8, "scope": "standalone full-angle graph contradiction"}


def exclusion(B, centers, masks, constants):
    cycle = find_cycle(B, inequalities(B, centers, masks, constants))
    if cycle is None:
        return None
    return {"cycle": cycle, "exact_cycle_check": verify_cycle(B, centers, masks, cycle, constants)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    margins = constants_gate(constants)
    args.output.write_text(json.dumps({
        "verified": True, "schema": "exact-n25-eight-rod-cap-v1", "N": 25,
        "angle_scale": constants["angle_scale"], "cap8": CAP8,
        "radius_threshold": constants["radius_upper"], "all_four_sine_margins": margins,
        "constants_sha256": sha(constants_path), "trig_source_sha256": sha(exact.kernel.ARCS / "exact_arcs.py"),
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    print("Exact eight-rod angle cap accepted:", CAP8, "/10000000", flush=True)


if __name__ == "__main__":
    main()
