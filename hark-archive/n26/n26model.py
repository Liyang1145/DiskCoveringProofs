"""Fresh, self-contained n=26 candidate-type 134-rod model + exact kernel gates.

The edge list was recovered (reconstruct_model.py) from the committed kernel
certificate and is checked here again against EVERY kernel used, by the exact
integer identity  L_FF(weights) * N == D * I  (no floats).

Vertices: 0..15 anchors, 16+c centers (c=0..25, boundary 0..15, interior 16..25),
42..75 face witnesses. Anchor j <-> centers j, j+1 (mod 16).
"""
import json
from fractions import Fraction as F

# R* upper end of the committed 60-digit enclosure (cover26/README.md)
RSTAR_UP = F("0.234700090400448239616790133776692127560495963654971391785925")
RSTAR_LO = F("0.234700090400448239616790133776692127560495963654971391785924")


def build_edges(partial):
    """partial: model_partial.json content -> full 134 edge list (edge order = weight order)."""
    edges = [tuple(e) if e else None for e in partial["edge_partial"]]
    rest = partial["anchor_rod_indices"]
    # center c has rods {x,y}; anchor j owns the two rods touching centers j and j+1
    owner = {}
    for c, (x, y) in partial["center_anchor_pairs"].items():
        owner.setdefault(x, set()).add(int(c)); owner.setdefault(y, set()).add(int(c))
    assert all(len(v) == 1 for v in owner.values())
    rodc = {e: next(iter(owner[e])) for e in rest}
    # rods come in consecutive index pairs (one anchor each); verify and assign
    for k in range(0, 32, 2):
        a, b = rest[k], rest[k + 1]
        ca, cb = rodc[a], rodc[b]
        j = ca if (ca + 1) % 16 == cb else cb if (cb + 1) % 16 == ca else None
        assert j is not None, (a, b, ca, cb)
        edges[a] = (j, 16 + ca); edges[b] = (j, 16 + cb)
    assert all(e is not None for e in edges) and len(set(map(lambda e: tuple(sorted(e)), edges))) == 134
    return edges


def laplacian(edges, weights, n=76):
    L = [[0] * n for _ in range(n)]
    for (u, v), w in zip(edges, weights):
        L[u][u] += w; L[v][v] += w; L[u][v] -= w; L[v][u] -= w
    return L


def kernel(edges, cert):
    """Exact gates as in the archived kernel_gate; returns Schur pair weights c_ij (Fractions),
    W (Fraction), harmonic rows (Fractions), resistances (Fractions)."""
    scale = cert["weight_scale"]; w = cert["weight_numerators"]
    assert len(w) == 134 and all(type(x) is int and x > 0 for x in w)
    L = laplacian(edges, w)
    Dn = int(cert["inverse_denominator"])
    N = [[int(v) for v in row] for row in cert["inverse_numerators"]]
    assert Dn > 0 and all(N[i][j] == N[j][i] for i in range(60) for j in range(60))
    for i in range(60):
        Li = L[16 + i]
        for j in range(60):
            if sum(Li[16 + k] * N[k][j] for k in range(60)) != (Dn if i == j else 0):
                raise AssertionError("exact ground inverse identity failed")
    H = [[-sum(N[i][k] * L[16 + k][j] for k in range(60)) for j in range(16)] for i in range(60)]
    assert all(min(r) >= 0 and sum(r) == Dn for r in H)
    S = [[L[i][j] * Dn + sum(L[i][16 + k] * H[k][j] for k in range(60)) for j in range(16)] for i in range(16)]
    assert all(sum(r) == 0 for r in S)
    assert all(S[i][j] == S[j][i] and (i == j or S[i][j] <= 0) for i in range(16) for j in range(16))
    den = scale * Dn
    pairs = {(i, j): F(-S[i][j], den) for i in range(16) for j in range(i + 1, 16) if S[i][j]}
    W = F(sum(w), scale)
    harm = [[F(H[i][j], Dn) for j in range(16)] for i in range(60)]
    res = [F(N[i][i] * scale, Dn) for i in range(60)]  # resistance in weight units 1/scale -> G^{-1} = N/Dn * scale? see note
    return {"pairs": pairs, "W": W, "harm": harm, "res": res, "scale": scale, "Dn": Dn, "N": N, "L": L}

# Note on units: L is built from integer weight numerators; physical weights are
# w/scale, so physical L_phys = L/scale and G_phys^{-1} = scale * N / Dn.
