"""Pure integer combinatorial generator for the n12/k9 witness-network graph inputs.

Scope: research-2026/n12-global/members/nine-topology/graphs.json (nine-topology member).
No floating point, no interval arithmetic, no metric numerics: only incidence, degree, Euler and
connectivity checks over small integers.  Conventions (matching lead/network_graph.py):

  rings     0..8, ring i lies between anchor i-1 and anchor i (mod 9)
  anchors   0..8, anchor i connects ring i and ring (i+1)%9; it is the boundary spoke of the outer
            triangle (i, (i+1)%9, labels[i])
  hubs      9..8+m  (m = 1,2,3)
  faces     triples of vertex indices; the face list is
            [9 outer triangles] + [inner (1 ring + 2 hubs) triangles] + [central (3 hubs) triangle if any]
  primal edges = 2-subsets occurring in some face; boundary edges = the 9 anchor pairs

Families and canonical representatives (derived in K9-TYPE-LIST.md section 2):
  M1                                 1 type
  M2(s1,s2)  s1+s2=9, s1,s2>=1       4 reps, canon under (s1,s2)~(s2,s1)
  T2(sA,sB)  sA+sB=9                 4 reps, canon under swap
  P4(s1,s2,s3,s4)  sum 9            20 reps, canon under the Klein four group
                                     {id, (s3,s4,s1,s2), (s1,s4,s3,s2), (s3,s2,s1,s4)}
  P3(sLp,sM,sL)    sum 9            16 reps, canon under (sLp,sM,sL)~(sL,sM,sLp)
  P2(sL,sLp)  sum 9                  4 reps, canon under swap
  T3(sA,sB,sC) sum 9                 7 reps (lead-owned, reproduced for a complete k9 catalogue)

Run: py -3 -B research-2026/n12-global/members/nine-topology/gen_graphs.py
"""
import json
from pathlib import Path
from itertools import permutations

HERE = Path(__file__).resolve().parent


def outer(labels):
    return [[i, (i + 1) % 9, labels[i]] for i in range(9)]


def make_M1():
    labels = [9] * 9
    return dict(id="M1", family="M1", m=1, parameters={}, hub_roles={"9": "h"},
                labels=labels, inner=[], central=[], faces=outer(labels))


def make_M2(s1, s2):
    labels = [9] * s1 + [10] * s2
    inner = [[s1, 9, 10], [0, 10, 9]]
    return dict(id="M2-%d-%d" % (s1, s2), family="M2", m=2, parameters={"s1": s1, "s2": s2},
                hub_roles={"9": "u", "10": "v"}, labels=labels, inner=inner, central=[],
                faces=outer(labels) + inner)


def make_T2(sA, sB):
    # blocks A^sA B^sB; transition ring sA carries the 2-step chain A,C,B;
    # transition ring 0 carries the 1-step chain B,A; hub C (11) has exactly one ring neighbour.
    labels = [9] * sA + [10] * sB
    inner = [[sA, 9, 11], [sA, 11, 10], [0, 10, 9]]
    central = [[9, 10, 11]]
    return dict(id="T2-%d-%d" % (sA, sB), family="T2", m=3, parameters={"sA": sA, "sB": sB},
                hub_roles={"9": "A", "10": "B", "11": "C (k=1)"}, labels=labels, inner=inner,
                central=central, faces=outer(labels) + inner + central)


def make_P4(s1, s2, s3, s4):
    labels = [9] * s1 + [10] * s2 + [11] * s3 + [10] * s4
    x1, x2, x3 = s1, s1 + s2, s1 + s2 + s3
    inner = [[x1, 9, 10], [x2, 10, 11], [x3, 11, 10], [0, 10, 9]]
    return dict(id="P4-%d-%d-%d-%d" % (s1, s2, s3, s4), family="P4", m=3,
                parameters={"s1": s1, "s2": s2, "s3": s3, "s4": s4},
                hub_roles={"9": "L", "10": "M", "11": "L'"},
                labels=labels, inner=inner, central=[], faces=outer(labels) + inner)


def make_P3(sLp, sM, sL):
    # blocks L'^sLp M^sM L^sL; the L->L' transition (ring 0) carries the 2-step chain L,M,L'
    labels = [11] * sLp + [10] * sM + [9] * sL
    x2, x3 = sLp, sLp + sM
    inner = [[0, 9, 10], [0, 10, 11], [x2, 11, 10], [x3, 10, 9]]
    return dict(id="P3-%d-%d-%d" % (sLp, sM, sL), family="P3", m=3,
                parameters={"sLp": sLp, "sM": sM, "sL": sL},
                hub_roles={"9": "L", "10": "M", "11": "L'"},
                labels=labels, inner=inner, central=[], faces=outer(labels) + inner)


def make_P2(sL, sLp):
    # both transitions carry 2-step chains; M (10) is adjacent to exactly the two transition rings
    labels = [9] * sL + [11] * sLp
    inner = [[sL, 9, 10], [sL, 10, 11], [0, 11, 10], [0, 10, 9]]
    return dict(id="P2-%d-%d" % (sL, sLp), family="P2", m=3, parameters={"sL": sL, "sLp": sLp},
                hub_roles={"9": "L", "10": "M", "11": "L'"},
                labels=labels, inner=inner, central=[], faces=outer(labels) + inner)


def make_T3(sA, sB, sC):
    labels = [9] * sA + [10] * sB + [11] * sC
    x1, x2 = sA, sA + sB
    inner = [[x1, 9, 10], [x2, 10, 11], [0, 11, 9]]
    central = [[9, 10, 11]]
    return dict(id="T3-%d-%d-%d" % (sA, sB, sC), family="T3 (lead-owned)", m=3,
                parameters={"sA": sA, "sB": sB, "sC": sC},
                hub_roles={"9": "A", "10": "B", "11": "C"}, labels=labels, inner=inner,
                central=central, faces=outer(labels) + inner + central)


# ---------- exact integer enumeration of canonical representatives ----------

def compositions(total, parts):
    """all tuples of `parts` positive integers summing to total (integer recursion)"""
    if parts == 1:
        if total >= 1:
            yield (total,)
        return
    for first in range(1, total - parts + 2):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def canon(orbits):
    return min(orbits)


def p4_orbits(t):
    s1, s2, s3, s4 = t
    return [(s1, s2, s3, s4), (s3, s4, s1, s2), (s1, s4, s3, s2), (s3, s2, s1, s4)]


def p3_orbits(t):
    a, b, c = t
    return [(a, b, c), (c, b, a)]


def pair_orbits(t):
    a, b = t
    return [(a, b), (b, a)]


# ---------- structural checks (integers only) ----------

def check(graph):
    m = graph["m"]
    labels, faces = graph["labels"], graph["faces"]
    nverts = 9 + m
    out = {}
    # faces are triples of distinct vertices in range, and exactly the declared list
    for f in faces:
        assert len(f) == 3 and len(set(f)) == 3
        assert all(0 <= v < nverts for v in f)
    assert [f[:] for f in faces] == graph["faces"]
    # primal edges from faces
    edges = set()
    for a, b, c in faces:
        for e in ((a, b), (b, c), (a, c)):
            edges.add(tuple(sorted(e)))
    F = len(faces)
    E = len(edges)
    boundary = set(tuple(sorted((i, (i + 1) % 9))) for i in range(9))
    interior = edges - boundary
    deg = {v: 0 for v in range(nverts)}
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    # face classification
    two_ring = one_ring = zero_ring = 0
    for f in faces:
        r = sum(1 for v in f if v < 9)
        h = 3 - r
        assert r <= 2 and h >= 1
        if r == 2:
            two_ring += 1
        elif r == 1:
            one_ring += 1
        else:
            zero_ring += 1
    # no RR edge except the boundary spokes
    for a, b in edges:
        if a < 9 and b < 9:
            assert tuple(sorted((a, b))) in boundary, "non-spoke ring-ring edge"
    # anchors appear in exactly one face each
    for e in boundary:
        cnt = sum(1 for f in faces if e[0] in f and e[1] in f)
        assert cnt == 1, ("anchor incidence", e, cnt)
    # ring vertex: faces at R_i = deg - 1 ; hub vertex: faces at h = deg
    hub_neigh = {i: sorted(v for v in range(9, nverts) if tuple(sorted((i, v))) in edges)
                 for i in range(9)}
    t_i = {i: len(hub_neigh[i]) for i in range(9)}
    for i in range(9):
        assert deg[i] == 2 + t_i[i], ("ring degree", i, deg[i], t_i[i])
    # hub graph connectivity (BFS, integer)
    hh = [(a, b) for a, b in edges if a >= 9 and b >= 9]
    seen, stack = {9}, [9]
    while stack:
        v = stack.pop()
        for a, b in hh:
            w = b if a == v else (a if b == v else None)
            if w is not None and w not in seen:
                seen.add(w)
                stack.append(w)
    assert len(seen) == m, "hub graph not connected"
    # Euler for the disk
    assert nverts - E + F == 1, ("euler", nverts, E, F)
    # rigid counts
    assert F == 7 + 2 * m, ("face count", F)
    assert E == 15 + 3 * m, ("edge count", E)
    assert len(boundary) == 9 and len(interior) == 6 + 3 * m
    assert two_ring == 9 and one_ring + zero_ring == 2 * m - 2
    assert zero_ring <= 1
    # transition-ring chains: for each ring, hub neighbours form a path in H and give t-1 inner faces
    for i in range(9):
        t = t_i[i]
        inner_at = [f for f in faces if i in f and sum(1 for v in f if v < 9) == 1]
        assert len(inner_at) == t - 1, ("inner faces at ring", i, len(inner_at), t)
        # the chain is a path: consecutive hubs in sorted-by-face order are adjacent in H
    out.update(dict(V=nverts, F=F, E=E, boundary_edges=9, interior_edges=len(interior),
                    faces_2ring=two_ring, faces_1ring=one_ring, faces_0ring=zero_ring,
                    deg_rings=[deg[i] for i in range(9)],
                    deg_hubs=[deg[9 + k] for k in range(m)],
                    hub_neighbours={str(i): hub_neigh[i] for i in range(9)},
                    hub_graph_edges=[list(e) for e in hh],
                    labels=labels))
    return out


def main():
    graphs = [make_M1()]
    for s1, s2 in sorted({canon(pair_orbits(t)) for t in compositions(9, 2)}):
        graphs.append(make_M2(s1, s2))
    for sA, sB in sorted({canon(pair_orbits(t)) for t in compositions(9, 2)}):
        graphs.append(make_T2(sA, sB))
    for t in sorted({canon(p4_orbits(t)) for t in compositions(9, 4)}):
        graphs.append(make_P4(*t))
    for t in sorted({canon(p3_orbits(t)) for t in compositions(9, 3)}):
        graphs.append(make_P3(*t))
    for sL, sLp in sorted({canon(pair_orbits(t)) for t in compositions(9, 2)}):
        graphs.append(make_P2(sL, sLp))
    for t in sorted({tuple(sorted(c)) for c in compositions(9, 3)}):
        graphs.append(make_T3(*t))

    # symmetry cross-check of the canonical counts
    counts = {}
    for g in graphs:
        counts[g["family"]] = counts.get(g["family"], 0) + 1
    assert counts["M1"] == 1 and counts["M2"] == 4 and counts["T2"] == 4
    assert counts["P4"] == 20 and counts["P3"] == 16 and counts["P2"] == 4
    assert counts["T3 (lead-owned)"] == 7
    for g in graphs:
        g["checks"] = check(g)
    payload = {
        "schema": "nine-topology/k9-network-graphs/v1",
        "provenance": {
            "source": "research-2026/n12-global/members/nine-topology/K9-TYPE-LIST.md section 2",
            "generator": "gen_graphs.py (pure integer incidence/degree/Euler/connectivity checks; no floats)",
            "complete_for": "k=9 branch, r<=U, abstract triangulated dual disk: M1 (1), M2 (4), P4 (20), "
                            "P3 (16), P2 (4), T2 (4); T3 (7) reproduced for completeness and marked "
                            "lead-owned",
        },
        "conventions": {
            "rings": "0..8; anchor i sits between ring i and ring (i+1)%9",
            "anchors": "9 anchors, anchor i = boundary spoke with outer triangle (i, (i+1)%9, labels[i])",
            "hubs": "9..8+m",
            "faces": "triples; list = 9 outer triangles + inner (1 ring + 2 hubs) + optional central (3 hubs)",
            "primal_edges": "2-subsets occurring in a face; the 9 anchor pairs are the boundary edges",
        },
        "consumption": {
            "nsites": "9+m",
            "network_graph": "network_graph.network_edges(faces) with nsites=9+m: anchor node nf+i joins "
                             "(i,(i+1)%9); face node nsites+j joins faces[j]",
            "not_in_this_file": "per-graph rational edge weights and the 9 reference angles theta are NOT "
                                "here; this file is structural only (lead's generalized certifier "
                                "proposes/verifies them)",
        },
        "family_counts": counts,
        "graphs": graphs,
    }
    (HERE / "graphs.json").write_text(json.dumps(payload, indent=1), encoding="utf-8")
    for g in graphs:
        c = g["checks"]
        print("%-14s m=%d F=%2d E=%2d int=%2d ring_deg=%s hub_deg=%s"
              % (g["id"], g["m"], c["F"], c["E"], c["interior_edges"], c["deg_rings"], c["deg_hubs"]))
    print("TOTAL", len(graphs), counts)


if __name__ == "__main__":
    main()
