# R20 FINAL REPORT — producer-faithful family, competition exchange (successor round)

Author: cline2 / DS v4.1f (successor of cline2-r20-gluing; single member, no sub-agents).
Scope: diagnostic instrument + one bounded negative reading. **No claim registered, no lead file
modified, no proof asserted.** All outputs under `research-2026/team-current/r20-gluing/`.

---

## 0. Object, caliber, source of truth

| item | value |
|---|---|
| allowance | **R = r_cand = 0.3799838531198388** (the saved candidate's own covering radius, `lead/q0_exact_closure_radius.json`). At R = 19/50 a strict cover exists, so the sharp-area support question is not even well posed there — the predecessor's readings at 19/50 are quarantined. |
| family | exactly `lead/q0_lower375_dual.py` (51 lines) + its certifier `lead/certify_q0_lower375.py` |
| factor value | `f_k(pi_k; z) = v_k(pi_k) + M_k(pi_k).z`, linear in z at fixed tuple (v_k = the primal area term, **not** z-scaled) |
| free parameters | **78** independent copies: 11 faces × (a,b,y), 9 switches × (b,y), 9 rings × (α,u,v) |
| ETA | **identically 0** in this family (producer line 15 `const[eta]=0`, line 44 `bounds[eta]=(0,0)`; certifier asserts `z[eta]==0`) |
| kappa | producer line 37 "no ear capacity constraint in q0"; the certifier asserts `z[50:71] >= 0` |
| lambda | `>= 0` in the producer's search; `Σw = 2π` is an equality, so it may be relaxed free |
| cone used | `z[eta]=0`, `z[50:71]>=0`, `z[71]>=0`, **all other columns free** |

## 1. Line-by-line audit of my family against the producer (`r20_prod_check.py`)

* ETA column (72) coefficients across all 29 factors: **0 nonzero → PASS**. (The earlier probe
  `r20_factor_probe.Model.ring_coefs` adds `+z[eta]` for rings i≥3; that is a *different* family,
  and the predecessor report's "ETA firing on rings 3–8" is hereby **withdrawn** as a claim about
  the producer family. `z[eta]=0` makes it numerically moot, but the structural statement was wrong.)
* kappa columns appear in M (42 entries) — consistent with the producer assembling them while
  having no ear constraint; the certifier pins them nonnegative.
* LAM appears in all 9 ring factors (the `M[:,lam]=w` term).
* **Value match at the candidate**: `const(z_c825) + Σ_k(v_k + M_k·z_c825) = π` to `3.1e-15`.
  This is the assembled identity (the dualized equalities the candidate satisfies cancel), i.e.
  slack bookkeeping — **not** a proof that `V` is a valid bound.
* Validity caveat stated explicitly: at a random tuple `V(z_c825;X) = 10.90`, but that tuple
  violates the constraint families (Σw ≠ 2π etc.), so it does **not** refute the bound. `V(z) ≥ π`
  is asserted only on the constraint-feasible set (the producer's sign-cone construction); that
  cone was assumed here and not independently re-derived.

## 2. Competition exchange (`r20_exchange.py`, `r20_exch2.py`) — the bounded reading

Procedure: seed the LP with competitor cuts; solve for z (feasibility form, candidate KKT rows
included); compute each factor's **true** maximiser `X_k*` on its own box (29 INDEPENDENT problems:
2D faces / 1D switches / 3D rings, grid + Nelder-Mead); add the 29 cuts; repeat, at most 10
exchanges. No continuum BnB, no joint 78-parameter search.

| scope | verdict | last-iteration worst factor excess |
|---|---|---|
| \|z\|∞ ≤ 3 (the producer's own documented bounds) | **no witness in 10 exchanges** | +8.9e-2 |
| \|z\|∞ ≤ 1e3 | **no witness in 10 exchanges** | +7.6e-2 |
| \|z\|∞ ≤ 1e6 | **no witness in 10 exchanges** | **+2.6e-2** |
| unbounded | no convergence; 27–29 new cuts per exchange | +0.1 … +0.3 |

Reading: at each exchange the LP still finds a z satisfying the accumulated cuts and the KKT rows,
but the *true* factor-wise maximisers beat the candidate by a positive margin; the margin shrinks
as the scope widens (+0.089 → +0.026) and never closes.

**Verdict: numerically inconclusive, leaning no-support.** The LP is reliably *feasible* (a
relaxation), but no reliable sharp witness emerged in 10 exchanges at any scope. This is **not**
upgraded to a disproof — the exchange is a finite cutting procedure and the margin is still
decreasing.

## 3. Corrections to the predecessor report (all acknowledged)

1. **The `V = 1092` reading was scoped wrongly.** It refuted one particular z, not the family; and
   `max` over tuples is not `min` over z, so a failed test at a fixed z proves nothing about the
   family. Withdrawn.
2. **No 78D branch-and-bound is needed or performed.** The 29 factors are independent, so the
   factor-wise maximisers are separate 1D/2D/3D problems. The predecessor's "next action" (78-param
   BnB) is withdrawn as unnecessary.
3. **ETA**: "ETA firing" is not a property of the producer family (ETA ≡ 0 there).
4. **`V ≤ π` is not an assembled identity** — it is the tightness requirement; the identity is the
   value match `V(z_c825;π*) = π`. Stated correctly in §1.
5. The predecessor's claim "the obstruction is global maximality, not stationarity" survives only
   as a *hypothesis* supported by §2's non-convergence, not as a measured dichotomy.

## 4. Scope guards (what is NOT claimed)

* No claim registered; nothing here is a proof of any radius bound; the lead kernel is untouched.
* The exchange verdict is a bounded, sampled statement about the producer family at `R = r_cand`.
  "No witness in 10 exchanges" is necessary-only evidence and is **not** a family-level disproof.
* The `|z| ≤ 3` scope is the documented scope of the saved dual family; wider scopes are reported
  for information, not as the natural object.
* Validity of `V(z) ≥ π` on the feasible set (producer cone) was assumed for the bound reading and
  is not independently re-derived here.
* Quarantined (wrong caliber / 69 shared parameters / homogeneous stationarity / reversed boundary
  signs / improvised cone): `quarantine/` — 13 files, non-bearing history.

## 5. Repro

```
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_toy_calibration.py   # sign/affine gates
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_prod_check.py        # producer audit + identity
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_producer_family.py   # 78-param rows (calib 1e-10)
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_exchange.py          # unbounded exchange
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_exch2.py             # scoped exchange (3 scopes)
```
Evidence: `r20_producer_instrument.json`, `r20_exch2.json`, `r20_exchange.json`, `r20_prod_check`
output, `r20_branch_calib.py` output.
