# DBM–LOCAL–NORM (r20-chain) — RETRACTIONS ONLY (no new certificate, no extra computation)

Assigned separable task; `lead/` untouched; no subagents.  This file now records **retractions and the
counterexample** requested by the lead (2026-09-25j).  Nothing here may be used as a bound or a route.

## R1. §3 of the previous version is RETRACTED — the "dual bound on `‖x‖²`" was invalid

I had written, for a cell `A x ≤ b` and `λ ≥ 0`,

> `max_{Ax≤b} ‖x‖² ≤ min_{λ≥0} [ λᵀb + ‖Aᵀλ‖²/4 ]`   ← **WRONG**

the completing-the-square identity `‖x‖² − λᵀ(Ax−b) = ‖x − Aᵀλ/2‖² + λᵀb − ‖Aᵀλ‖²/4` has its
**minimum** at `x = Aᵀλ/2`, not its maximum; the right-hand side grows like `‖x‖²` and is therefore
**unbounded above** over `x ∈ R^n`.  Taking `λ = 0` would "give" `max‖x‖² ≤ 0`.

**Counterexample (as the lead supplied it).**  Cell `x ∈ [0,1]`, i.e. `A = 1`, `b = 1`: the true value
is `max‖x‖² = 1`, while the retracted formula with `λ = 0` returns `0 < 1`.  So the bound is false and
**must not be applied** to the 118 open cells (nor elsewhere).  A correct convex-quadratic *maximum*
over a polytope needs a genuinely different device (e.g. exact vertex enumeration), and no such device
is claimed here.

Status of the earlier "component box" remark: the box is *not* "a special case of the retracted bound";
that framing is withdrawn as well.  Nothing in this file asserts any `‖x‖²` bound.

## R2. §1 of the previous version is RETRACTED — wrong hypothesis form

The already-proven pinned theorem's hypothesis is **`‖raw8 x‖ ≤ ρ`** (the raw eight-angle perturbation
in the pinned chart), **not** `‖P x‖ ≤ ρ`.  I had written the projection-based form
`‖x_perp‖ = ‖Px‖` as the transfer hypothesis; that is **not** the proven statement, and I did **not**
prove any projected theorem.  Consequently:

* no transfer of the pinned certificate to other pinnings or to an arbitrary gauge is asserted;
* the identity `‖Px‖² = ‖x‖² − ⟨x,u⟩²` is an algebraic identity only and is **not** used as a route here.

## R3. Recorded facts (measurements, not certificates)

* **Cyclic shifts are not automorphisms.**  On the explicit 51-edge incidence of the fixed-oracle
  graph, shifting the anchor labels by `k = 1,…,8` never maps the edge set to itself.  Hence the nine
  pin choices are not the same graph problem.  (This is the check the lead required; it is recorded as a
  measurement only.)
* **Correct reflection (as stated by the lead, recorded verbatim):** the true reflection is
  **hub fixed**, **site `4 − i`**, **anchor `3 − i`** — not a hub swap.  My earlier speculation about a
  hub swap was wrong and is withdrawn; no claim is made about which pinnings it relates, and no
  certificate transfer is asserted from it.

## R4. What this file now contains

Only: the two retractions (R1, R2) with the counterexample, and the recorded measurements/symmetry data
(R3).  No new certificate, no projected-theorem claim, no `‖x‖²` bound, no additional computation.
