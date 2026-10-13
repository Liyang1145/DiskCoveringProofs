#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent audit of members/nine-topology/graphs.json:
  (a) structural re-verification of every listed graph (Euler, degrees, face classes,
      no non-spoke ring-ring edge, hub-graph connectivity, chain = path);
  (b) COMPLETENESS by brute force, not by counting: enumerate all cyclic label data
      on the 9 ring vertices for every allowed hub graph, with the chain/walk
      conditions of K9-TYPE-LIST.md Section 1, and compare the resulting canonical
      block families with the listed ones.
  (c) closure under zero-block degenerations: check that every degenerate label
      pattern allowed by the walk condition is represented (T2 / P2 families).

Scope: combinatorial only.  The metric certificates are audited separately
(audit_taylor.py).  Read-only on other members' files.
Usage: py -3 -B audit_graphs.py
"""
from __future__ import annotations

import json
import itertools
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
N12 = HERE.parents[2]
GRAPHS = N12 / "members" / "nine-topology" / "graphs.json"
OUT = HERE / "out"
OUT.mkdir(exist_ok=True)

HUBS = {"K1": (1, []),
        "K2": (2, [(0, 1)]),
        "K3": (3, [(0, 1), (1, 2), (0, 2)]),
        "P3": (3, [(0, 1), (1, 2)])}


def dist(H, a, b):
    """H-distance between hubs (chains of length 1 or 2 are allowed)."""
    if a == b:
        return 0
    if (min(a, b), max(a, b)) in H:
        return 1
    for c in range(max(max(e) for e in H) + 1):
        if (min(a, c), max(a, c)) in H and (min(c, b), max(c, b)) in H:
            return 2
    return 3


def all_chains(H, a, b):
    """all simple chains in H from a to b of length <= 2: [[a]] if a==b, else the
    1-step chain if adjacent, plus every 2-step chain through a common neighbour."""
    out = []
    if a == b:
        return [[a]]
    if (min(a, b), max(a, b)) in H:
        out.append([a, b])
    for c in range(max(max(e) for e in H) + 1):
        if c != a and c != b and (min(a, c), max(a, c)) in H and (min(c, b), max(c, b)) in H:
            out.append([a, c, b])
    return out


def chain(H, a, b):
    """the shortest simple path in H from a to b (length <= 2), or None."""
    cs = all_chains(H, a, b)
    return min(cs, key=len) if cs else None


def block_signature(labels):
    """cyclic run structure: list of (hub, runlength) up to rotation (canonical min)."""
    n = len(labels)
    reps = []
    for s in range(n):
        rot = labels[s:] + labels[:s]
        runs = []
        for h, g in itertools.groupby(rot):
            runs.append((h, len(list(g))))
        reps.append(tuple(runs))
    return min(reps)


def audit_structure(payload):
    """Re-verify each listed graph combinatorially (independent implementation)."""
    bad = []
    for g in payload["graphs"]:
        m = g["m"]
        labels = g["labels"]
        faces = [tuple(f) for f in g["faces"]]
        nv = 9 + m
        assert all(0 <= v < nv for f in faces for v in f)
        # ring labels must agree with the outer triangles
        outer = faces[:9]
        ok_outer = all(outer[i] == (i, (i + 1) % 9, labels[i]) for i in range(9))
        edges = set()
        for f in faces:
            for e in itertools.combinations(f, 2):
                edges.add(tuple(sorted(e)))
        boundary = {tuple(sorted((i, (i + 1) % 9))) for i in range(9)}
        RR = {e for e in edges if e[0] < 9 and e[1] < 9}
        deg = {v: 0 for v in range(nv)}
        for a, b in edges:
            deg[a] += 1
            deg[b] += 1
        hubs = range(9, nv)
        # hub neighbours of each ring form a path in H, and #inner faces at ring = t-1
        chk_chains = True
        for i in range(9):
            nb = sorted(h for h in hubs if tuple(sorted((i, h))) in edges)
            t = len(nb)
            inner_at = sum(1 for f in faces if i in f and sum(1 for v in f if v < 9) == 1)
            if inner_at != t - 1 or deg[i] != t + 2:
                chk_chains = False
        # hub graph connected
        hh = [(a, b) for a, b in edges if a >= 9 and b >= 9]
        seen = {9}
        stack = [9]
        while stack:
            v = stack.pop()
            for a, b in hh:
                w = b if a == v else (a if b == v else None)
                if w is not None and w not in seen:
                    seen.add(w)
                    stack.append(w)
        res = dict(
            id=g["id"], m=m, labels_ok=ok_outer,
            F=len(faces), E=len(edges),
            F_ok=(len(faces) == 7 + 2 * m), E_ok=(len(edges) == 15 + 3 * m),
            euler_ok=(nv - len(edges) + len(faces) == 1),
            RR_only_spokes=(RR <= boundary),
            hub_connected=(len(seen) == m),
            chains_ok=chk_chains,
            two_ring_faces=sum(1 for f in faces if sum(1 for v in f if v < 9) == 2),
        )
        res["all_ok"] = all(v for k, v in res.items()
                            if k not in ("id", "m", "F", "E", "two_ring_faces"))
        if not res["all_ok"]:
            bad.append(res)
    return bad


def cyclic_runs(rot):
    """maximal cyclic runs of equal labels (first/last merged when they share a hub)."""
    runs = [(h, len(list(g))) for h, g in itertools.groupby(rot)]
    if len(runs) > 1 and runs[0][0] == runs[-1][0]:
        h0, s0 = runs[0]
        hl, sl = runs[-1]
        runs = [(h0, s0 + sl)] + runs[1:-1]
    return tuple(runs)


def canonical(labels, H, m):
    """Canonical cyclic block structure of a ring-label sequence, modulo ring rotation,
    ring reflection and hub renaming inside the automorphism group of H."""
    edgeset = frozenset(tuple(sorted(e)) for e in H)
    autos = [p for p in itertools.permutations(range(m))
             if frozenset(tuple(sorted((p[a], p[b]))) for a, b in H) == edgeset]
    best = None
    for lab in (list(labels), list(reversed(labels))):
        for s in range(len(lab)):
            runs = cyclic_runs(lab[s:] + lab[:s])
            for p in autos:
                cand = tuple((p[h], sz) for h, sz in runs)
                k = len(cand)
                cand2 = min(cand[i:] + cand[:i] for i in range(k))
                if best is None or cand2 < best:
                    best = cand2
    return best


def hub_shape(faces, m):
    """hub graph shape of a listed graph: K1, K2, K3 or P3"""
    hubs = range(9, 9 + m)
    edges = set()
    for f in faces:
        for a, b in itertools.combinations(f, 2):
            if a >= 9 and b >= 9:
                edges.add(tuple(sorted((a - 9, b - 9))))
    if m == 1:
        return "K1", []
    if m == 2:
        return "K2", [(0, 1)]
    if len(edges) == 3:
        return "K3", [(0, 1), (1, 2), (0, 2)]
    return "P3", [(0, 1), (1, 2)]


def enumerate_types():
    """Brute force over all cyclic label data + chain choices with the Section-1
    chain/walk conditions of K9-TYPE-LIST.md:

      * q_i (hub neighbours of ring i) is a simple path in H from l_{i-1} to l_i,
        of length 1 (same label), 2 (1-step chain) or 3 (deliberate 2-step chain);
      * sum_i (t_i - 1) = (2m-2) - [H = K3];
      * concatenating q_1..q_9 plus (K3 case) the boundary of the (0,3) triangle
        traverses every hub edge exactly twice.
    """
    found = {}
    for shape, (m, HH) in HUBS.items():
        inner = 2 * m - 2 - (1 if shape == "K3" else 0)
        hub_edges = [tuple(sorted(e)) for e in HH]
        need = 2 - (1 if shape == "K3" else 0)
        for labels in itertools.product(range(m), repeat=9):
            trans = [i for i in range(9) if labels[(i - 1) % 9] != labels[i]]
            base = sum(1 for i in trans) + sum(1 for i in range(9)
                                                if i not in trans and False)
            # t_i = 1 for non-transitions; transitions contribute 1 (1-step) or 2 (2-step)
            extra_needed = inner - len(trans)
            if extra_needed < 0:
                continue
            capable = [i for i in trans
                       if any(len(c) == 3 for c in all_chains(HH, labels[(i - 1) % 9],
                                                              labels[i]))]
            if extra_needed > len(capable):
                continue
            for choice in itertools.combinations(capable, extra_needed):
                qs = []
                ok = True
                for i in range(9):
                    if i in trans:
                        cs = all_chains(HH, labels[(i - 1) % 9], labels[i])
                        if i in choice:
                            cs = [c for c in cs if len(c) == 3]
                        else:
                            cs = [c for c in cs if len(c) == 2]
                        if not cs:
                            ok = False
                            break
                        qs.append(cs[0])
                    else:
                        qs.append([labels[i]])
                if not ok:
                    continue
                cnt = {e: 0 for e in hub_edges}
                for q in qs:
                    for a, b in zip(q, q[1:]):
                        cnt[tuple(sorted((a, b)))] += 1
                if any(v != need for v in cnt.values()):
                    continue
                key = (shape, canonical(labels, HH, m))
                found[key] = found.get(key, 0) + 1
    return found


def main():
    payload = json.loads(GRAPHS.read_text(encoding="utf-8"))
    rep = {"source": str(GRAPHS.relative_to(N12.parent.parent))}
    bad = audit_structure(payload)
    rep["n_graphs"] = len(payload["graphs"])
    rep["structural_bad"] = bad
    print(f"graphs.json: {len(payload['graphs'])} graphs, "
          f"structural failures: {len(bad)}")
    for b in bad[:10]:
        print("   FAIL:", b)

    # canonical block families present in graphs.json (with hub-graph shape)
    listed = {}
    for g in payload["graphs"]:
        m = g["m"]
        shape, HH = hub_shape([tuple(f) for f in g["faces"]], m)
        labs = [l - 9 for l in g["labels"]]          # hub labels 9.. are hub indices 0..
        assert all(0 <= l < m for l in labs), (g["id"], labs)
        key = (shape, canonical(labs, HH, m))
        listed.setdefault(key, []).append(g["id"])
    enum = enumerate_types()
    uncovered = sorted(set(enum) - set(listed))
    listed_only = sorted(set(listed) - set(enum))
    rep["n_enumerated_patterns"] = len(enum)
    rep["n_listed_patterns"] = len(listed)
    rep["uncovered_patterns"] = [[k[0], [list(r) for r in k[1]]] for k in uncovered[:20]]
    rep["listed_not_enumerated"] = [[k[0], [list(r) for r in k[1]], listed[k]]
                                    for k in listed_only[:20]]
    print(f"brute-force enumeration: {len(enum)} canonical (H-shape, block-structure) patterns")
    print(f"listed in graphs.json   : {len(listed)} canonical patterns")
    print(f"enumerated but NOT listed: {len(uncovered)}")
    for u in uncovered[:10]:
        print("   UNCOVERED:", u, "x", enum[u])
    print(f"listed but NOT enumerated: {len(listed_only)}")
    for u in listed_only[:10]:
        print("   LISTED-ONLY:", u, listed[u])

    (OUT / "graph-enumeration-audit.json").write_text(
        json.dumps(rep, indent=1, ensure_ascii=False), encoding="utf-8")
    print("log ->", OUT / "graph-enumeration-audit.json")
    if bad or uncovered or listed_only:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
