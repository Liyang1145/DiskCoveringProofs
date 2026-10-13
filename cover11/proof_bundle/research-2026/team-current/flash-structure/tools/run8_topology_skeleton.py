"""Run 8: combinatorial audit of the ring-locality topology skeleton (own instruments).

Rules used (proved elsewhere):
  R1  dual disk: 9 ring vertices on the boundary (in the 9-cycle order), 2 hubs interior;
  R2  every face is a triangle (trivalent);
  R3  LOCALITY: in every face, any two RING vertices have cyclic index distance <= 2
      (a Voronoi vertex x in D is covered, so the ring disks sharing x pairwise intersect,
       and intersecting ring disks have index distance <= 2 by the locality lemma);
      hub-ring and hub-hub pairs are unrestricted.
  R4  the hub-hub edge exists (d = 1, capacity bridge);
  R5  ring-only faces are exactly consecutive triples (i,i+1,i+2)  [same rule R3 + C_9^2 clique = 3].

Checks:
  A) the 8-gon {0,2,3,4,5,6,7,8} cannot be triangulated with ring-only (consecutive) triangles;
  B) ears (i,i+1,i+2) use the two boundary edges (i,i+1),(i+1,i+2); a boundary edge of the dual
     disk lies in exactly one face, so ears are pairwise edge-disjoint -> q <= floor(9/2) = 4;
  C) counts: with d = 1, q = c = 13 - K, core faces = 11 - q = K - 2d; every core triangle
     contains a hub.
"""
import itertools
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

OUT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "out"))
os.makedirs(OUT, exist_ok=True)
rep = []
def P(*a):
    s = " ".join(str(x) for x in a)
    rep.append(s)
    print(s)


def triangulations(poly):
    """all triangulations of the convex polygon with vertex list poly (cyclic order),
    returned as frozenset of triangles (tuples of vertices).  Standard recursion on the
    triangle containing the edge (poly[0], poly[1]); count = Catalan(n-2)."""
    poly = list(poly)
    n = len(poly)
    if n < 3:
        return [frozenset()]
    if n == 3:
        return [frozenset([tuple(sorted(poly))])]
    out = []
    for k in range(2, n):
        left = poly[1:k + 1]
        right = [poly[0]] + poly[k:]
        tri0 = frozenset([tuple(sorted((poly[0], poly[1], poly[k])))])
        for t1 in triangulations(left):
            for t2 in triangulations(right):
                out.append(t1 | t2 | tri0)
    return out


def main():
    # ---------------- A: the 8-gon after a skip-one chord
    W = [0, 2, 3, 4, 5, 6, 7, 8]          # ring indices on the long side of chord (0,2)
    tri = triangulations(W)
    P(f"[A] triangulations of the 8-gon {W}: {len(tri)} (Catalan(6) = 132)")
    ok = []
    for T in tri:
        if all((abs((a - c + 9) % 9) if False else True) for a, ct, c in [(0, 0, 0)]):
            pass
        good = True
        for (a, b, c) in T:
            if len({a, b, c}) != 3:
                good = False
                break
            # consecutive triple test (mod 9)
            s = sorted((a, b, c))
            if not ((s[1] - s[0] == 1 and s[2] - s[1] == 1) or (s == [0, 7, 8])
                    or (s == [0, 1, 8]) or (s[0] == 0 and s[1] == 7 and s[2] == 8)):
                # general cyclic test
                okc = any(sorted(((v + t) % 9) for v in (a, b, c)) == [0, 1, 2] for t in range(9))
                if not okc:
                    good = False
                    break
        if good:
            ok.append(T)
    P(f"[A] triangulations of the 8-gon whose faces are all CONSECUTIVE triples: {len(ok)}")
    P(f"[A] => the 'long side without hubs' is impossible: {len(ok) == 0}")

    # ---------------- B: ear packing on the 9-cycle
    ears = [tuple(sorted(((i + t) % 9) for t in (0, 1, 2))) for i in range(9)]
    edges = [(i, (i + 1) % 9) for i in range(9)]
    ekey = {tuple(sorted(e)): k for k, e in enumerate(edges)}
    sets = []
    for r in range(0, 6):
        for S in itertools.combinations(range(9), r):
            used = {}
            bad = False
            for i in S:
                for e in ((i, i + 1), (i + 1, i + 2)):
                    k = ekey[tuple(sorted((e[0] % 9, e[1] % 9)))]
                    if k in used:
                        bad = True
                    used[k] = i
            if not bad:
                sets.append(S)
    P(f"[B] edge-disjoint ear sets on C_9: {len(sets)} (by size: "
      f"{ {r: sum(1 for S in sets if len(S) == r) for r in range(6)} })")
    P(f"[B] max ears q <= {max(len(S) for S in sets)} (= floor(9/2))")

    # ---------------- C: counts consistency
    P("[C] counts (d = 1: hub-hub edge exists; K = k1+k2, q ring-only faces, c chords):")
    P("    identities used: 42 = 18 + 2c + (K-2) + K  =>  c + K = 13 ;  q = 11 - K + 2 = 13 - K")
    for K in range(6, 14):
        c = 13 - K
        q = 13 - K
        if K - 4 < c:      # c <= K - 4d  (each chord has a hub end)
            continue
        P(f"    K={K}: c={c}, q={q}, core faces = 11-q = {11-q} = K-2d  "
          f"(chord-end bound c <= K-4 = {K-4} ok)")
    P("[C] hence q in {0,1,2,3,4} and K = 13 - q in {9,...,13}; the record configuration has "
      "K=13, q=c=0")
    with open(os.path.join(OUT, "run8_topology_skeleton.txt"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(rep) + "\n")


if __name__ == "__main__":
    main()
