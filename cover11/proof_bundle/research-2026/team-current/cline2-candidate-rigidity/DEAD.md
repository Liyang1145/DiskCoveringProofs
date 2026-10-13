# cline2-candidate-rigidity — DEAD / method limits (2026-09-24, round 4)

Scope: this directory only. Separates (A) implementation failures, (B) method limits and
(C) mathematical negatives. Nothing here kills a *mathematical* proposition about the
n11 target unless labelled (C).

## A. Implementation failures (do not cite the affected numbers)

0. **SECTOR-HEIGHT-OBSTRUCTION.md is fully retracted (lead-rejected 2026-09-24).** Wrong
   ring-centre norm (`r` instead of `sqrt(1-r^2)`), wrong full-width value, `Σα = 2π` instead
   of `2π + 2Σb`, false identity `α = w/2`, false obligation (EX), false hub criterion. See
   `INVALID.md` for the itemised table and the corrected reference data. **The whole
   sector-height/degeneracy line is stopped**; (EX) must not be encoded anywhere.

## B. Implementation failures (continued, bisector bug)

1. **Two bisector parametrisations, one of them wrong (my own bug, fixed).** The perpendicular
   bisector of sites `i,j` is `p . (c_i - c_j) = (|c_i|^2 - |c_j|^2)/2`. Two of my scripts
   solved the *opposite* linear equation (`p . (c_j - c_i) = ...`), which produces the
   antipodal branch: "boundary spokes" at distances `0.31–0.72` instead of `R`, and spurious
   pairs `(8,6)`, `(3,10)`. Affected files: `out/verify_71.py`, `out/spokes.py`,
   `out/spokes_exact.py`, `out/boundary_fixed.py`, `tools/boundary_crit.py` (first half),
   `tools/crit_set.py` (the spoke loop), `tools/second_order.py`, `tools/second_order2.py`,
   `tools/slsqp_min.py`, `tools/flat_family.py`, `tools/nullspace_probe.py`,
   `tools/grad_danskin*.py`, `tools/jac23.py`, `tools/jac_tight.py`. Those outputs are
   **void**. The verified single-parametrisation computation is `tools/active_verified.py`
   (with `tools/boundary_crit2.py`, `tools/boundary_final.py`, `tools/final_active.py`,
   `tools/three_radii.py`). All load-bearing numbers in STATUS.md/EQUALITY-MECHANISM.md were
   re-derived with `tools/active_verified.py`.
   *(Note: several of the void scripts still give correct **rank/nullity** numbers because
   their constraint sets were only re-labelled, but their tight-point values are not usable.)*
2. **Mixing double-precision `int/1e17` with 50-dps mpmath** produced complex `acos`
   arguments (|arg| = 1+2e-17) and, in one script, a bogus critical value `0.7306` (a
   non-critical point reached by the buggy bisector). Fix: build the centres with
   `mpmathify(string)` / exact rationals, and clamp never — compare at the verified
   precision instead.
3. **`tools/gamma_and_min.py` third bullet and `out/minprobe.py`**: the "max over the
   critical set" there scanned the *wrong* boundary set (bisector bug, item 1) and returned
   values `0.42–0.73`. Void. The Nelder–Mead runs in those scripts optimised the corrupted
   objective; their conclusion ("gamma can be lowered") is an artifact and **must not** be
   read as a counterexample to the candidate.
4. **My 60-dps minimal-norm Newton solve** of the 18 tight-point equations
   (`tools/solve_rstru_mp.py`) converged to `R = 0.384513497186650560…`, residual `1e-62`,
   with centre displacements ~1e-1. Keep only as evidence that the 18-point system is a
   larger solution set; it is **NOT** an argument against the existence of a dual certificate
   at the candidate (see B.2).

## C. Method limits (true statements about instruments, not about mathematics)

1. **Sampled maxima are not bounds.** A 200k-point scan of `bd D` gave
   `0.37998356089092689`, i.e. `3e-7` *below* the true maximum. Never quote a grid/dense-scan
   maximum as a covering bound (agrees with flash-geometry DEAD).
2. **The obstruction to a tight-point certificate is a rank deficit, not non-uniqueness.**
   At the candidate the 18 tight-point equalities have rank 18 in 23 variables, i.e.
   codimension 4 (nullity 5 = 4 tangent + 1 gauge), matching the lead's independent
   tangent dimension 4 in the 63-variable closure system (rank 59). The existence of *other*
   solutions of the same equations elsewhere in configuration space is logically irrelevant
   to a **local** certificate at the candidate (my earlier text said the opposite; corrected).
3. **Sub-1e-15 separations are meaningless in double precision.** The tight-point values agree
   with `C529` only to `~1e-16` in doubles; meaningful 30-digit statements require the
   60-dps path (mpmath, exact rational centres).
4. **q0(6,7) is the same configuration as the saved upper witness** — hub degrees (7,6),
   no ears — so no *new* candidate is produced by this round; the value studied is the
   existing certified upper object's chart, not a new search.

## D. Mathematical negatives / open (do not over-read)

1. **Not dead: global optimality.** Nothing in this round refutes or proves
   `r_D(11) >= C529`. The active set is necessary only.
2. **CLOSED (was flagged, now void): the `+7.9e-17` "anomaly".** I had compared the saved
   object's radius with the KKT-witness literal `T_cert`; the lead resolved it — `T_cert`
   (C249 ⇒ C830) belongs to `research-2026/session2/n11alg/cert_sym60.json`, a **different
   1e−60 object**, while the saved object's radius is `C529 = 0.3799838531198387090485182…`
   which **matches its registered interval and is reproduced by the registered verifier**
   (`research-2026/session2/lead/verify_config.py n11/upper/certified_object.json` →
   `0.379983853119838709048518179573`, attribution V2b). No discrepancy exists; the naming
   rule is: saved object = `C529`, never `T_cert`/`R_stru`.
3. **Rotation/symmetry:** no exact 9-fold or 180° symmetry was found (ring moduli differ:
   `0.7009, 0.7618, 0.7009, 0.8588, 0.8209, 0.7618, 0.8588, 0.8209, 0.8925`); do not invoke
   one. Any future argument must remain asymmetric.
