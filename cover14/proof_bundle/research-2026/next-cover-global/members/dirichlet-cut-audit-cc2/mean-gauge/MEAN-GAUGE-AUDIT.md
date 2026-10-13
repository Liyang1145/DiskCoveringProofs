# MEAN-GAUGE-AUDIT — analytic interface audit of the q10 mean-angle gauge

Member `dirichlet-cut-audit-cc2`, scope `members/dirichlet-cut-audit-cc2/mean-gauge/` (no existing
bearing file touched). Objects: `lead/Q10-MEAN-GAUGE.md`, `q10_mean_gauge_control.py`,
`q10_mean_gauge_audit.py`, `q10_metric_mean_round_audit.py` (plus `q10_mean_gauge_bound.py`).
Repro for the exact checks here: `mean_gauge_identity_check.py`. No bound recomputation; the two
finite controls remain the lead's own double-arithmetic evaluations.

Verdict: **no soundness defect found; accept with four documentation/assertion caveats.** The
mean-gauge value is a *valid* lower bound at each vertex (dual bound at a rotated representative with
a re-solved balanced flow), the all-vertex concave-minorant coverage still holds, and the branch/η
machinery is internally consistent. What is *inaccurate* is the doc's framing (see §2), not the code.

## 1. Algebra: verified exactly (coefficient identity, not numerics)

With `s_j = Σ_{i<j} d_i` and `m = (1/10)Σ_{r=0..9} s_r`, the definition
`θ'_j = jL − s_j + m` is *identical* per anchor to the audit's direct affine formula
`θ'_j = jL + Σ_i[(9−i)/10 − 1_{i<j}] d_i`:

* `mean_gauge_identity_check.py` compares the two coefficient vectors for all ten anchors — equal;
* the summed d-coefficients vanish identically, so `Σ_j θ'_j = 45L` **exactly**;
* `d_9` has coefficient 0 in *every* `θ'_j` (it never lies under a prefix), so the identity uses
  `Σ_{i≤8}(9−i)d_i` — the code's `m` (sum over the ten prefix intervals including `s_0 = 0`) and the
  audit's formula agree precisely, including that disappearance.

## 2. "Common rotation may be configuration-dependent?" — yes, but it is not a gauge of the value

* It *is* a common rotation *within* a configuration: the same `m(d)` is added to every `j`. Allowing
  `m` to depend on `d` is legitimate because the whole system is rotation-invariant: the C1281
  witness constraints `‖c_v − A_e‖ ≤ r`, the face/owner incidence, and the deficit polytope
  (`d ≥ 0`, `Σd = D`, the C1332–C1334 slab/triple/pair constraints) are invariant under a global
  rotation, so rotating each configuration (sites *and* anchors) keeps it in the same class.
  Verified by `if t0[j] < 0` behaviour and by the gauge tag carried in the certificate.
* It is **not** a gauge of the code's functional. `gauge_replay` evaluates a *real* dot product at the
  anchors `A(θ'_j)` — i.e. at the rotated anchors — and re-solves the balanced flow for those anchors.
  Only the *modulus* form `|Σ_j g_j e^{iθ_j}|` is rotation-invariant; a real-part/anchored form is
  not. Hence the anchor0 and mean-prefix runs compute two *different* valid certificates, and the
  doc's "can retain an artificial common-rotation contribution in interval angle widths" understates
  what changes: the *value* changes too, not just the interval widths.
  (Both values are valid lower bounds for the same `r`, so either may be used with the standard
  convention: a valid lower bound above the fixed `U` excludes, any other value is only
  inconclusive. The `min` inside `q10_metric_mean_round_audit.checked_replay` is something else — see
  §6 — it is the min of the *two arithmetic evaluations of the same mean certificate*.)

## 3. All-vertex concave-minorant coverage: still holds

Let `F(θ') = Σ_j [g_j·A(θ'_j) − (η_j/2)(θ'_j − t0_j)²]`. Each term has second derivative
`−g_j·A(θ'_j) − η_j`:

* in the `η_j = ‖g_j‖` branch, `g_j·A ≥ −‖g_j‖` gives `≤ 0` — concave;
* in the `η_j = 0` branch the selector requires `g_j·A ≥ 0` at both ends of the *hull* of the
  vertices' angle intervals **and** `hi − lo < π`. That pair of conditions is sufficient for
  `g_j·A ≥ 0` on the whole hull: the positivity set of `θ ↦ g_j·A(θ)` is a single open semicircle, so
  an interval of length `< π` whose two endpoints lie in it lies entirely in it (leaving and returning
  would need length `> π`). Hence the term is concave there too.

`θ'(d)` is affine in `d`, so `F` is concave on the polytope; the saved vertex set is complete (the
round audit re-decodes each polytope and compares the certificate's vertex set *exactly*), the η hull
is built from those same vertices, and the per-index lift is a function of `t0` only, hence identical
for every vertex. Therefore min over vertices = min over the polytope. Coverage is intact.

## 4. Unwrapped branch, endpoint signs, η

* The stored reference `angle_center_radians` is a **wrapped** representation with exactly one jump:
  measured `[0.22096, 0.885998, 1.442629, 2.115413, 2.691013, −2.927117, −2.262044, −1.689452,
  −1.016705, −0.444113]`, i.e. indices 5…9 negative.
* `gauge_replay` lifts per index (`if t0[j] < 0: t −= 2π`), and it does so with the
  *same* rule in `q10_mean_gauge_audit.dyadic`. Because the rule depends only on the saved `t0`, the
  lift is constant across vertices: the candidate's representation matches the stored one and the
  deviation `dt = t − t0` used in the penalty is the honest difference *in that convention*, not a
  2π-offset artefact. (A naive "unwrapped increasing" reading of `θ'` would have produced
  `dt ≈ ±2π` for five anchors and mis-scaled the penalty; the per-index lift prevents that. Note from
  §4's correction below: even such a mis-scaling would only weaken the value, never invalidate it.)
* **Correction (lead), accepted — `t0` is free; same-gauge is a quality/provenance requirement, not a
  soundness condition.** Mathematically `t0_j` may be *any* fixed real number: subtracting
  `(η_j/2)(θ'_j − t0_j)²` is always a minorant, and the second derivative `−g_j·A − η_j` does not
  depend on `t0_j` at all. Likewise any *fixed* per-`j` lift by `2π` is always valid: the first term
  `g_j·A(θ'_j)` is `2π`-periodic, so the lift changes neither it nor the η selector's positivity check
  (also `2π`-periodic) nor the hull length `hi − lo`; only the penalty's magnitude changes, and a
  subtracted penalty can only weaken a bound that is already valid. So a mixed gauge or a different
  lift **cannot** make the reported value invalid; the effect is at most a weaker value, and the
  *relative comparison* between two evaluations need not even be monotone. What the same-gauge choice
  buys is meaning and provenance: `dt` then equals the physical deviation, so the value is comparable
  with the reference-based growth statement. The code does keep the frame consistent (the mean-gauge
  certificate carries mean-gauge angles, tag `gauge = "mean_prefix"`), which is good practice to
  record rather than a soundness necessity.
* η criterion: endpoint positivity is *sufficient* only together with the `hi − lo < π` assertion,
  which is present in both scripts but documented nowhere. Recommend recording it with the η rule.

## 5. Old-replay usage: checked, no misuse of stale output as evidence

* `q10_metric_mean_round_audit.checked_replay` dispatches on the gauge tag: mean-gauge certificates go
  to `gauge_replay` **and** `dyadic` with the reported value being their `min`, other certificates go
  to the audited `replay` under `assert "gauge" not in c`. No mixing. The `min` is between the two
  *arithmetic evaluations of the same mean certificate* (Fraction and direct dyadic), i.e. two lower
  ends of one quantity — not a min over anchor0/mean certificates. **Correction (lead), accepted.**
* The anchor0 control value is *asserted* equal to the audited replay
  (`assert str(low) == old['lower_radius_exact']`), a genuine provenance check.
* All reported lower bounds are recomputed; the round audit additionally asserts that each
  certificate's vertex set equals the independently re-clipped polytope. No saved bound is reused as
  evidence.
* **Correction (lead), accepted — the unconditional `fr.replay(rec)` call is not dead code.** It
  rebuilds `faces`/`owners`/`incidence` and asserts exact balance, and the new mean-gauge functional
  *depends* on those assertions; only its returned *value* is unused in the mean branch. It should be
  kept, with its purpose documented (removing it would drop the centre-balance validation).
* **Correction (lead), accepted — the graph-automorphism transport transports inequalities.** The
  records built through `q10-fan-transport.json` are transported inequality cuts, relying on the
  existing exact graph-automorphism verification, not merely a label canonicalization. They remain
  candidate records (only complete cases, none registered), but their status is "transported
  inequality", which is stronger than what this report first said.
* Fixed-U check: the control flags are consistent with `U = 0.33173203427623414` (old 0.33171880 and
  new 0.33172429 both below it → `excluded = False`; near-threshold new 0.33173236 above it → `True`),
  so there is no evidence of the forbidden substitution by the output-flow lower bound 0.34774679
  (DEAD.md line 58).

## 6. The two finite controls (numbers, explicitly not proofs)

| cell | anchor0 bound | mean-gauge bound | outcome |
|---|---|---|---|
| `q10-metric-round3-2.json` node 0 | 0.3317188030617438 | 0.33172429212885385 | both < U → inconclusive (as the artifact's status says) |
| near-threshold | 0.33173192754747266 | 0.33173236108454085 | crosses U → excluded |

Two caveats: (i) the two numbers are values of **different functionals** (§2), so "improvement" means
"a better valid certificate", not "the same bound with tighter intervals"; (ii) the Fraction and
direct-dyadic evaluations share the branch rule, the flow construction and the `t0` source, so their
agreement validates the *arithmetic kernels* only — it cannot validate the gauge or branch choices.
Exactly as the lead said: numerical agreement is not proof. (The `min` reported by `checked_replay` is
between these two evaluations of the *same* mean certificate, not a min over two gauges.)

## 7. Accepted range and required follow-ups

Accepted: the mean-gauge kernel is a valid (revised) certificate generator; per-configuration rotation
is legitimate; coverage, branch and η are sound; `t0` may be any fixed real and any fixed per-index
`2π` lift is valid, so no choice here can make the reported value invalid; nothing here contradicts
C1356/C1352 or any registered claim, and no registered cut depends on it. All three corrections the
lead raised are incorporated above (free `t0`/lift as a quality rather than soundness condition; the
`min` inside `checked_replay` is intra-certificate; `fr.replay` is a live validation dependency).

Remaining suggestions, documentation only (no computation needed):
1. reword `Q10-MEAN-GAUGE.md`: the gauge changes the *functional* (rotated anchors + re-solved flow),
   so state comparisons as "two valid certificates"; note that only the modulus form is
   rotation-invariant. Keep the same-gauge requirement as a *provenance/quality* rule, and note that
   `t0` and the per-index lift are otherwise free;
2. document that `gauge_replay`'s `fr.replay(rec)` call is retained for its `faces`/`owners`/incidence
   reconstruction and exact-balance assertions, with only its value unused in the mean branch;
3. record the η rule together with its `hi − lo < π` companion condition (endpoint positivity alone
   is not sufficient without it).

No exclusion may be registered from these controls alone; a new tree-level exclusion would need the
same provenance as before (complete vertex sets, same-gauge reference, unmodified fixed U).
