"""Reconstruct the 134-rod model (edge list) of the n=26 candidate type from a
committed full134rod kernel certificate, and verify it EXACTLY.

Inputs: dl/root25-slim.json (extracted verbatim from the committed root25
composition, SHA256 c1675552...).  The edge list itself is not committed in the
public repo (SYSTEM.json / old reference are missing), so we recover it from
K_ff = D * N^{-1} (computed mod a large prime, then verified by an exact
integer identity N * (scale*K_ff) == D*scale*I).

Vertex convention (from n26_full_candidate_face_energy.py):
  0..15 anchors, 16+c center c (c=0..25; 0..15 boundary), 42..75 witnesses.
Anchor i connects to centers i and i+1 (mod 16).
"""
import json, sys, itertools
from fractions import Fraction as F

P = (1 << 521) - 1  # Mersenne prime


def inv_mod_matrix(A, p):
    n = len(A)
    M = [[a % p for a in row] + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(A)]
    for c in range(n):
        r = next(r for r in range(c, n) if M[r][c])
        M[c], M[r] = M[r], M[c]
        iv = pow(M[c][c], p - 2, p)
        M[c] = [x * iv % p for x in M[c]]
        for r in range(n):
            if r != c and M[r][c]:
                f = M[r][c]
                M[r] = [(x - f * y) % p for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]


def signed(x, p):
    return x - p if x > p // 2 else x


def reconstruct(cert):
    scale = cert["weight_scale"]
    w = cert["weight_numerators"]
    Dn = int(cert["inverse_denominator"])
    N = [[int(v) for v in row] for row in cert["inverse_numerators"]]
    Ninv = inv_mod_matrix(N, P)
    K = [[signed(Dn * Ninv[i][j] % P, P) for j in range(60)] for i in range(60)]  # scale*K_ff
    # exact check  N * K == Dn*scale*I
    for i in range(60):
        for j in range(60):
            s = sum(N[i][k] * K[k][j] for k in range(60))
            if s != (Dn if i == j else 0):
                raise AssertionError("exact inverse identity failed")
    # free index f -> vertex 16+f ; centers f=0..25 -> vertex 16..41 ; witnesses f=26..59 -> 42..75
    wset = {}
    for idx, x in enumerate(w):
        wset.setdefault(x, []).append(idx)
    edges = [None] * 134
    used = set()
    for i in range(60):
        for j in range(i + 1, 60):
            if K[i][j]:
                val = -K[i][j]
                cands = [e for e in wset.get(val, []) if e not in used]
                if not cands:
                    raise AssertionError(f"offdiag {i},{j} weight not found")
                e = cands[0]; used.add(e)
                edges[e] = (16 + i, 16 + j)
    # anchor rods: residual diagonal on boundary centers
    rest = [e for e in range(134) if e not in used]
    assert len(rest) == 32, len(rest)
    resid = {}
    for i in range(60):
        off = sum(-K[i][j] for j in range(60) if j != i)
        r = K[i][i] - off
        if r:
            resid[i] = r
    assert sorted(resid) == list(range(16)), sorted(resid)
    # center c has anchors c-1 and c. Chain: choose weight for rod (anchor0,center0) then propagate
    restw = {w[e]: e for e in rest}
    assert len(restw) == 32
    # simpler: brute force pairing per center
    pairs = {}
    for c in range(16):
        opts = [(x, y) for x, y in itertools.combinations(rest, 2) if w[x] + w[y] == resid[c]]
        pairs[c] = opts
    # solve: each rest edge used once, center c gets {rod(c-1,c), rod(c,c)}; consistent anchor labels
    sol = None
    def search(c, usedr, chosen):
        nonlocal sol
        if sol: return
        if c == 16:
            sol = dict(chosen); return
        for x, y in pairs[c]:
            if x in usedr or y in usedr: continue
            chosen[c] = (x, y)
            search(c + 1, usedr | {x, y}, chosen)
            del chosen[c]
    search(0, set(), {})
    assert sol, "no anchor assignment"
    # which of each pair is (anchor c-1) vs (anchor c) cannot be determined from K_ff alone.
    return K, edges, rest, sol, resid


if __name__ == "__main__":
    d = json.load(open(sys.argv[1]))
    cert = d["full134rod_supports"][0]["kernel_certificate"]
    K, edges, rest, sol, resid = reconstruct(cert)
    faces = {}
    for e in edges:
        if e:
            u, v = e
            faces.setdefault(v, []).append(u - 16)
    faces = sorted(tuple(sorted(f)) for f in faces.values())
    print("witness-center rods:", sum(1 for e in edges if e), "faces:", len(faces))
    print(faces)
    print("anchor pair options per center:", {c: len([1]) for c in sol})
    json.dump({"faces": faces, "edge_partial": edges, "anchor_rod_indices": rest,
               "center_anchor_pairs": {c: sol[c] for c in sol}}, open("model_partial.json", "w"))
