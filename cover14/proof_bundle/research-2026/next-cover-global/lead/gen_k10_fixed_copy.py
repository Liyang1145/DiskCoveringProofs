"""Pure integer enumerator for the n12/n14 dual-disk topology catalogues (calibrated).

Scope: research-2026/next-cover-global/members/topology/ (companion of K10-TOPOLOGY-DESIGN.md).
Conditional inputs for N=10 (n14 k=10/11): (K1) k10 boundary cells connected, (K2) non-adjacent ring
DISKS disjoint (stronger than cells disjoint; not an equivalence), (K4) coverage at r<=U; not re-audited here.
No floats, no interval arithmetic: integer incidence/link/Euler checks only.

Rings 0..N-1, hubs N..N+m-1.  Counts on the fan-triangulated T (not on the untriangulated G):
  V = N+m, F = N+2m-2, E = 2N+3m-3, interior edges = N+3m-3, outer triangles = N, inner = 2m-2,
  hub-only triangles H3 = E_HH - m + 1 (forced).
Fan triangulation convention: fan each face from a HUB vertex, so no artificial edge joins two rings
(no ring chord is ever introduced; a 2-ring face is the spoke face whose ring pair is already adjacent).

Calibration: N=9, m<=3 must reproduce the 56 entries of the n12 catalogue (compared up to canonical form).
"""
import json
import sys
import time
from collections import defaultdict
from itertools import combinations, permutations
from pathlib import Path

HERE = Path(__file__).resolve().parent


def ekey(a, b):
    return (a, b) if a < b else (b, a)


def cliques3(edges):
    out = []
    verts = sorted(set(v for e in edges for v in e))
    for tri in combinations(verts, 3):
        if all(ekey(a, b) in set(map(tuple, map(sorted, edges))) for a, b in combinations(tri, 2)):
            out.append(tri)
    return out


def skeletons(N, m):
    """(name, edges, hub_only_triangles) for connected H on m vertices with H3 = E_HH - m + 1."""
    def pack(name, edges, tri_choices):
        E = len(edges)
        H3 = E - m + 1
        cl = cliques3(edges)
        sets = [c for c in combinations(range(len(cl)), H3)] if H3 >= 0 else []
        out = []
        for sel in sets:
            tris = [cl[i] for i in sel]
            ok = True
            cnt = defaultdict(int)
            for t in tris:
                for a, b in combinations(t, 2):
                    cnt[ekey(a, b)] += 1
            for e in edges:
                if cnt[ekey(*e)] > 2:
                    ok = False
            if ok:
                out.append((name, edges, tris))
        return out

    if m == 1:
        return [("K1", [], [])]
    if m == 2:
        return [("K2", [(0, 1)], [])]
    if m == 3:
        return pack("P3", [(0, 1), (1, 2)], None) + pack("K3", [(0, 1), (1, 2), (0, 2)], None)
    if m == 4:
        out = []
        out += pack("P4", [(0, 1), (1, 2), (2, 3)], None)
        out += pack("K13", [(0, 1), (0, 2), (0, 3)], None)
        out += pack("C4", [(0, 1), (1, 2), (2, 3), (3, 0)], None)     # expect: excluded (no triangle)
        out += pack("K3P", [(0, 1), (1, 2), (0, 2), (0, 3)], None)
        out += pack("diamond", [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)], None)
        out += pack("K4", [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], None)
        return out
    raise ValueError(m)


def euler_walks(multi, start):
    inst = []
    for e, c in multi.items():
        inst.extend([e] * c)
    adj = defaultdict(list)
    for idx, (a, b) in enumerate(inst):
        adj[a].append(idx)
        adj[b].append(idx)
    total = len(inst)
    seen_walks = set()
    out = []

    def rec(v, used, path):
        if len(path) == total + 1:
            if v == start:
                t = tuple(path)
                if t not in seen_walks:
                    seen_walks.add(t)
                    out.append(list(path))
            return
        for idx in adj[v]:
            if idx in used:
                continue
            a, b = inst[idx]
            w = b if a == v else a
            used.add(idx)
            path.append(w)
            rec(w, used, path)
            path.pop()
            used.remove(idx)

    rec(start, set(), [start])
    return out


def compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest

def build(N, m, sk_edges, hub_only, walk, cuts):
    """returns face tuple or None (checks: types, edge incidence, links, Euler)."""
    S = len(walk) - 1
    starts = [0]
    for L in cuts:
        starts.append(starts[-1] + L)
    for i in range(N):
        seg = walk[starts[i]:starts[i + 1] + 1]
        if len(set(seg)) != len(seg):
            return None
    l = [walk[starts[i + 1]] for i in range(N)]
    faces = [(i, (i + 1) % N, N + l[i]) for i in range(N)]
    for i in range(N):
        for k in range(starts[i], starts[i + 1]):
            faces.append((i, N + walk[k], N + walk[k + 1]))
    for t in hub_only:
        faces.append((N + t[0], N + t[1], N + t[2]))
    for f in faces:
        if len(set(f)) != 3:
            return None
        nring = sum(1 for v in f if v < N)
        if nring > 2:
            return None
        if nring == 2 and not (abs(f[0] - f[1]) in (1, N - 1)):
            return None
    cnt = defaultdict(int)
    edges = set()
    for f in faces:
        for a, b in combinations(f, 2):
            cnt[ekey(a, b)] += 1
            edges.add(ekey(a, b))
    spokes = set(ekey(i, (i + 1) % N) for i in range(N))
    for e, c in cnt.items():
        if e in spokes:
            if c != 1:
                return None
        elif c != 2:
            return None
    V, E, F = N + m, len(edges), len(faces)
    if (V, E, F) != (N + m, 2 * N + 3 * m - 3, N + 2 * m - 2):
        return None
    if V - E + F != 1:
        return None
    face_at = defaultdict(list)
    for idx, f in enumerate(faces):
        for v in f:
            face_at[v].append(idx)
    for v in range(V):
        nbr = defaultdict(set)
        for idx in face_at[v]:
            o = [x for x in faces[idx] if x != v]
            nbr[o[0]].add(o[1])
            nbr[o[1]].add(o[0])
        if v >= N:  # hub: link must be one cycle
            if len(nbr) != len(face_at[v]):
                return None
            if not nbr:
                return None
            start = min(nbr)
            first = min(nbr[start])
            seen, prev, cur = [start, first], start, first
            while cur != start:
                nxts = [x for x in nbr[cur] if x != prev]
                if len(nxts) != 1:
                    return None
                nxt = nxts[0]
                if nxt == start:
                    break
                if nxt in seen:
                    return None
                seen.append(nxt)
                prev, cur = cur, nxt
            if len(seen) != len(nbr):
                return None
        else:       # ring: link must be a path from v-1 to v+1
            left, right = (v - 1) % N, (v + 1) % N
            if left not in nbr or right not in nbr:
                return None
            if len(face_at[v]) != len(nbr) - 1:
                return None
            ends = sorted(x for x in nbr if len(nbr[x]) == 1)
            if len(nbr) == 2:
                if sorted([left, right]) != ends:
                    return None
            else:
                if ends != sorted([left, right]):
                    return None
                # single path: walk from left to right visiting all
                seen, cur, prev = [left], left, None
                while cur != right:
                    nxts = [x for x in nbr[cur] if x != prev]
                    if len(nxts) != 1:
                        return None
                    nxt = nxts[0]
                    if nxt in seen and nxt != right:
                        return None
                    seen.append(nxt)
                    prev, cur = cur, nxt
                if len(seen) != len(nbr):
                    return None
    hh = set(ekey(a, b) for a, b in edges if a >= N and b >= N)
    if hh != set(ekey(N + a, N + b) for a, b in sk_edges):
        return None
    return tuple(sorted(faces))


def cheap_key(N, faces):
    best = None
    for sh in range(N):
        for refl in (False, True):
            img = []
            for f in faces:
                out = []
                for v in f:
                    if v < N:
                        w = (v + sh) % N
                        if refl:
                            w = (sh - v) % N
                        out.append(w)
                    else:
                        out.append(v)
                img.append(tuple(sorted(out)))
            key = tuple(sorted(img))
            if best is None or key < best:
                best = key
    return best


def full_canon(N, m, faces):
    best = None
    for perm in permutations(range(m)):
        relab = tuple(N + perm[v - N] if v >= N else v for v in range(N + m))
        for sh in range(N):
            for refl in (False, True):
                img = []
                for f in faces:
                    out = []
                    for v in f:
                        w = relab[v]
                        if w < N:
                            x = (w + sh) % N
                            if refl:
                                x = (sh - w) % N
                            out.append(x)
                        else:
                            out.append(w)
                    img.append(tuple(sorted(out)))
                key = tuple(sorted(img))
                if best is None or key < best:
                    best = key
    return best


def run(N, m, budget_s=10000.0):
    t0 = time.time()
    per_skel = {}
    phase1 = {}
    for name, sk_edges, hub_only in skeletons(N, m):
        E_HH = len(sk_edges)
        assert len(hub_only) == E_HH - m + 1
        t_e = defaultdict(int)
        for tri in hub_only:
            for a, b in combinations(tri, 2):
                t_e[ekey(a, b)] += 1
        multi = {}
        for a, b in sk_edges:
            c = 2 - t_e[ekey(a, b)]
            assert 0 <= c <= 2
            if c:
                multi[(a, b)] = c
        S = sum(multi.values())
        assert S == 2 * m - 2 - len(hub_only)
        starts = sorted(set(a for e in multi for a in e)) if multi else [0]
        found = 0
        for start in starts:
            for walk in euler_walks(multi, start):
                if time.time() - t0 > budget_s:
                    print("  [budget] skeleton %s stopped" % name)
                    break
                for cuts in compositions(S, N) if N else []:
                    T = build(N, m, sk_edges, hub_only, walk, cuts)
                    if T is None:
                        continue
                    found += 1
                    k = cheap_key(N, T)
                    if k not in phase1:
                        phase1[k] = dict(m=m, skeleton=name, faces=[list(f) for f in k])
        per_skel[name] = per_skel.get(name, 0) + found
    final = {}
    for k, e in phase1.items():
        fc = full_canon(N, m, [tuple(f) for f in e["faces"]])
        final.setdefault(fc, dict(m=m, skeleton=e["skeleton"], faces=[list(f) for f in fc]))
    return per_skel, len(phase1), len(final), final, time.time() - t0


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "calib"
    if which == "calib":
        Ns, ms = [9], [1, 2, 3]
    elif which == "k11":
        Ns, ms = [11], [3]      # k=11 branch: 14-11 = 3 hub disks, no merging possible
    else:
        Ns, ms = [10], [3, 4]
    report = {}
    for N in Ns:
        for m in ms:
            per_skel, p1, p2, final, dt = run(N, m)
            print("N=%d m=%d raw=%s phase1=%d catalogue=%d time=%.1fs"
                  % (N, m, per_skel, p1, p2, dt))
            for fc, e in final.items():
                report.setdefault((N, m), {})[fc] = e
    total = sum(len(v) for v in report.values())
    print("TOTAL catalogue:", total)
    out = {("%d/%d" % k): list(v.values()) for k, v in report.items()}
    (HERE / ("k-catalogue-%s.json" % which)).write_text(json.dumps(out, indent=1), encoding="utf-8")

