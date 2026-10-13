# Adaptive-stress ball kernel: source-level audit (r20-rigidity)

Object: `lead/certify_adaptive_stress_ball.py` + `lead/ADAPTIVE-STRESS-FINITE-REMAINDER.md`
(C891 exact root, C909/C912 carrying graph: 45 edges, 9 anchors, 20 free nodes).
**Scope of this audit: source-level consistency of the code with the analytic lemma.** I did *not*
re-evaluate the interval constants independently (that needs the C912 kernel data `N, G8, H, X,
alpha, U, edges`, i.e. a reconstruction; reading the certificate JSON is not enough, as the lead
states). No claim_review (C914-next not registered).

## Item-by-item check (code vs lemma)

| # | item | code | verdict |
|---|---|---|---|
| 1 | `MM` = **anchor flux change**, not `2 x flux` | `MM[2*node+c, j] += sgn*Q[e,j]*dd[c]` with `dd = X[v]-X[w]`; `l0[2*node+c] += sgn*alpha[e]*dd[c]` | **consistent**: the lemma uses `l_alpha = l0 + Mx` and puts the factor 2 in the *term* `2<l0+Mx, delta>`, so `M` must be the bare flux change. No spurious factor 2 in `MM`. |
| 2 | `Q = tau N G^T` | `Q = tau*k.N*G.T` with `G = k.G8` | **consistent**. (Shapes are self-consistent: the script ran to completion.) |
| 3 | `HH = H + 2 tau G G^T` | `HH = H + 2*tau*G*G.T` | **consistent** with lemma condition 4 (`H0 + 2 tau GG^T >= mu I` on the raw-8 chart). |
| 4 | `d >= max anchor-incident Laa weight` | anchor-incident edges only (`if node >= 9: continue`), `diag[node] += alpha[e]`, `ddiag = max hi(diag)` | **consistent**; and `Lambda0 = Laa - Laf Lff^{-1} Lfa <= Laa <= dI` is a valid quadratic-form bound because `Laf Lff^{-1} Lfa` is PSD. |
| 5 | `b >= max_e ||Q_e|| / alpha0_e` (relative to **each** weight) | `bdiag = max_e hi(||Q[e,:]|| / alpha[e])`; assertion `max(...) <= I(bQ)` | **consistent**: `(Qx)_e = <Q_e, x>` gives `abs((Qx)_e) <= ||Q_e|| ||x||`, so dividing by the *edge's own* `alpha0_e` is exactly the lemma's condition 1. |
| 6 | radial positivity + C909 stationarity | `arad[i] = sum_c l0[2i+c]*U[i][c]`, `assert min lo(arad) > 0` | **consistent, and stronger than needed** (lemma asks `a_i >= 0`, code asserts `> 0`). Stationarity/equal-carrying-length content is a *premise* (`k` + C909), not verified in this script — the script's `premises` field states this. |
| 7 | preconditioned SPD check for `HH - mu I` | `A = arr(base)`, `Cn = inv(cholesky((A+A.T)/2)).T`, `test = C^T base C`, interval Gershgorin margin `min_i lo(test_ii - sum_{j!=i}|test_ij|) > 0` | **logically valid**: the preconditioner is *any* concrete invertible matrix; a congruence preserves inertia (Sylvester), so `test > 0` implies `base > 0`; the interval Gershgorin margin is an outward-rounded lower bound (`lo(a-b) = lo(a)-hi(b)`), hence conservative. **Note:** `C` itself is built from float64 (`k.arr`) and then used as a fixed matrix; `C` is *not* symmetric (it is `L^{-T}`), so "SPD" applies to the preconditioned matrix, not to `C`. That is harmless for the argument but should not be quoted as "the preconditioner is SPD". |
| 8 | `m >= ||M||` for `||Mx||_F <= m||x||` | `mdiag = hi(sqrt(sum_{i,j} MM[i,j]^2))` (Frobenius) | **consistent** (`||M x||_F <= ||M||_F ||x||`). |
| 9 | remainder coefficient and radius conditions | `C3 = d(1+b) + m`; `assert b*rho < 1` and `C3*rho <= mu/4`; `rho_num = floor(lo(mu/(4 C3)) * 1e6)`, `assert rho_num >= 1`; growth `mu/4 = 1/2000` | **consistent** with the lemma's final line, including the *re-check* of the two inequalities after rounding down. |
| 10 | ceilings | `bQ = ceil(bdiag)`, `mQ = ceil(1000*mdiag)`, `dQ = ceil(1000*ddiag)` + three interval assertions comparing the raw quantities against the rational ceilings | **consistent** (the ceilings are re-verified by interval comparisons rather than trusted from `ceil`). |

## Errors found

**None in the ten items above.** Two statements that must not be made about this artifact (both are
wording, not mathematics):

1. "the preconditioner is SPD" — the used matrix is `L^{-T}` (non-symmetric); what is certified is
   `HH - mu I > 0` via a congruence + interval Gershgorin.
2. "MM was independently verified to be the flux change" — this audit establishes *source-level*
   consistency with the lemma; the numeric re-evaluation of `b, m, d, mu, rho` requires rebuilding the
   C912 kernel data and was **not** done here.

## Premise boundary

The script consumes the C912 kernel `k` (which encodes `N, G8, H, X, alpha, U, edges` at the exact
root) and the C909 stationarity/equal-carrying-length statement. Those are premises of this
certificate; nothing in this audit verifies them. The lemma itself is being audited by another member;
the local/global distinction in the lemma's "Status" line is correctly stated (local, not a global
reduction).
