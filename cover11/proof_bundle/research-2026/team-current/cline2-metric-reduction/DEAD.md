# DEAD (own directory) — scoped self-errors

## R17-E3 (Round 17, final): ENTIRE R17 geometry report nonbearing; false attribution retracted

**Object:** `NEXT-IMPLICATION-FLAT-EXCLUSION.md` and `WITHDRAWAL-R17.md` in full, plus the six
`r17_*.py` artifacts. All marked **NONBEARING**; no usable geometry (see `R17-NONBEARING.md`).

**Errors**

1. **False attribution (retracted).** `WITHDRAWAL-R17.md` attributed the flat width `2 asin(r/2)`
   to the lead. The lead never stated this. The correct flat width is `2 asin r` with chord `2r`,
   as in C842's proof.
2. **Wrong family.** My "exact" isosceles configuration (site equidistant from both endpoint
   sites, `h = r sin(eps/2)`, `w = 2 asin(r cos(eps/2))`) is not the general actual sector; it
   holds only under the extra hypothesis that both endpoint distances are `r`, which is not the
   situation C842's argument addresses. Consequences: the derived `eps ~ sqrt(delta)` law, the
   collar widths and the height-projection recommendation in `WITHDRAWAL-R17.md` §3/§4 are void.
3. **Process.** Three successive rounds of "corrected" geometry from me, each superseding the
   last, with no independent check of which configuration was being modelled. Stopping was the
   right call and I should have stopped after the first withdrawal rather than producing a new
   model of the same object.

**Control / replacement:** the lead's `NEAR-FLAT-SECTOR-GEOMETRY.md` supplies the valid inequality
version for asymmetric actual sectors and states the missing domain projection. Nothing of mine is
to be used for that object.

**Lesson (transferable):** when a derivation is ruled nonbearing, stop modelling — do not produce a
"corrected" model of the same object in the next round. Each re-modelling round multiplies the
chance of introducing a new false premise (here: an attribution) into the record.

## R17-E2 (Round 17): flat-limit deformation formulas and the C842 epsilon assertion

**Object:** the deformation section of `NEXT-IMPLICATION-FLAT-EXCLUSION.md` (now superseded by
`WITHDRAWAL-R17.md`).

**Withdrawn claims and reasons**

1. Flat limit of the sector width = `2 asin r` — **false**: at exact flatness the site is at the
   chord midpoint and `|P1P2| = r`, so the site's arc width tends to `2 asin(r/2)`.
2. `eps = 2 arcsin(delta/(2 sin(w/2)))` — no such identity; extrapolated, not derived.
3. `h = sqrt(delta(2r-delta))` — wrong; exact is `h = r sin(eps/2)` (`v = r cos(eps/2)`,
   `u = h = r sin(eps/2)` from the law of cosines in the isosceles triangle `M P+ P-`).
4. "`h/eps -> const`, hence a linear collar" — false in the chord-deficit variable: `delta` is
   **quadratic** in `eps`, so `eps ~ sqrt(delta)` and `h/delta -> infinity`; the constant `0.190`
   is the coefficient of `h/eps`, an `O(1)` ratio in the other variable.
5. The scan `r17_2_flat_limit.py` as evidence — **void**: it forced `|site - Pj| = r` for both
   endpoints with the chord endpoints fixed; the physical family has `|M Pj| = r` only at the two
   switch points, so the scan measured a non-physical subfamily.
6. "C842 bounds `alpha2 <= pi - 1e-8`" — **invented**. `claim_get C842`: scope "two endpoint
   sector boundary branches", statement covers endpoints 0 and 4 only, and its scope line says
   "other 7 sector degeneracies not excluded".

**Root cause:** I extrapolated a limit and a scaling from two numbers without enforcing the
constraints, then quoted a claim whose actual scope I had not read. The signature was that my
"calibration" produced a smooth constant where the geometry says the ratio must diverge — a
divergence is exactly what a mis-parametrised family hides.

**Control:** the exact closed form `h = r sin(eps/2)`, `w = 2 asin(r cos(eps/2))` (two lines from
the law of cosines and the unit-circle constraints), plus `claim_get C842`'s own scope string.

**Lesson (transferable):** (i) read the claim, not the summary, before using a bound; (ii) when a
quantity is supposed to diverge, a numerically stable constant means the parametrisation is
wrong, not that the analysis is right; (iii) always check which lengths the constraints pin
(all switches at radius `r`, not all chord endpoints).

## R15-E1 (2026-09-25): width-fiber envelope recipe — withdrawn at report level

**Object:** `WIDTH-FIBER-ENVELOPE.md` (Round 15) and the recipe
`max_b fiber <= S_b(b_lo) + r s sin(2b_lo)(b_hi - b_lo) + max{G(g), G(W(b_hi))}`.

**Root cause:** a scope-of-dependence error. I assumed `G` depends on `b` only through the
window; in fact `c, p, x, eta, u` are all functions of `b`, so the two-variable sensitivity was
silently reduced to a one-variable one. Compounded by two further errors:

1. I used `b <= acos r < pi/4` for `r in [3/8, 19/50]`; the true value is
   `acos(0.38) = 1.1810 rad > pi/4 = 0.7854`, so `sin 2b` is not increasing on the domain and
   the chord bound built on it is invalid.
2. I asserted that the maximum of `G` over the window is attained at an endpoint; `dG/dw`
   changes sign and the saved width-1 fibre has an **interior maximum** (lead's counterexample).

**Scoped consequence:** the recipe, the decomposition, the endpoint-maximum inference and the
`W'(b)` expression I quoted are void and must not be used or implemented. The 40-box calibration
is void as support (it calibrated a bound built on false premises). No claim was registered, so
no ledger retraction is needed; this is a report-level withdrawal.

**Independent control:** the lead's saved width-1 fibre with an interior maximum of `G`
(a direct counterexample to the endpoint-maximum inference), plus the arithmetic fact
`acos(0.38) > pi/4` (checkable in one line).

**Not dead / retained:** the exact *implicit partial* `b`-derivative block in
`WITHDRAWAL-R15.md` §3 (component-wise verified to `1e-8` against central differences):
`c_b = (-2r cos 2b, -2r sin 2b)`, `p_b = c_b·P`, `x_b = c_b×P`, `cn_b = -4r cos(2b+phi)`,
`dd_b = cn_b - 2p_b`, `u_b = dd_b/(2R0²u)`, `eta_b = ((1-p)x_b + x p_b)/D`, and the assembled
`dS/db|_w`, `dS/dw|_b`. These are identities, not bounds.

**Lesson (transferable):** before claiming "X depends on b only through Y", enumerate every
symbol in the expression and check its dependence individually; and never assert monotonicity of
`sin 2b` without checking `2b` against `pi/2` on the actual domain.
