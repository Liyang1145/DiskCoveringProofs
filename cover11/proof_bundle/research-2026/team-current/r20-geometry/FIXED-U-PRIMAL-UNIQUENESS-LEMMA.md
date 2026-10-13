# Fixed-`U` primal minimizer uniqueness at the candidate (lemma + reachability + compactness)

Author: r20-geometry (sole writer of this directory; no subagents; **no claim registered**).
Companion code: `fixed_u_primal_uniqueness.py/.out.txt` (exact combinatorial reachability on supplied dual
data; self-test included). For `gluing` (C902 → SOCP outer local minimal).

## 0. Setting (fixed switches)

Anchors `U = (U_0..U_8)` fixed (the switches); free primal nodes `X` = the nine sites `c_i` plus the
eleven face vertices `z_f`; edges `E` = the 18 boundary constraints `|c_i − U_{i−1}|, |c_i − U_i| ≤ t` plus
the 33 face constraints `|c_s − z_f| ≤ t` (`lead/FIXED-SWITCH-SOC-REDUCTION.md` §2; squared form with `t`).
**Notation (fixed once and for all).** `t` is the **squared** variable: constraints `|X_v − X_w|² ≤ t`,
value `V(U)² = t`, edge **lengths** `√t`. At the candidate write `t* = R²` for the squared value and
`R = √t*` for the length. (Earlier drafts mixed `R` and `R²`; corrected here.)

Candidate data (to be supplied by the oracle output): `X*`, `t* = R²`, and dual multipliers `α_e ≥ 0` with
the dual force vectors `p_e` (divergence-free, `Σ_e|p_e| ≤ 1`, tight at the optimum).

## 1. Hypotheses and the combinatorial premise (symbolic, no dual data needed)

The edge set `E` has **51** edges (18 endpoint + 33 face-incidence). Only some are active:

* **(H1′) Active-set form (corrected).** Let `E⁺ = {e : p_e ≠ 0}` be the edges with **strictly positive**
  dual force. By complementary slackness these are exactly the active edges, `|X*_v − X*_w| = R`; the
  slacked edges (6 of them by the fixed-switch bookkeeping) carry zero force and pin nothing. The literal
  "all 51 strictly positive" is **not** required and is not true; the export of `cline2-r23-gluing`
  (40 positive / 11 zero) is a *numerically weaker* reading of the same structure and is used only as an
  optional cross-check (§3).
* **(H2′) Non-degeneracy — supplied by C909, not by my float reading.** `p_e ≠ 0` on `E⁺` and the dual
  budget is tight, `Σ_e|p_e| = 1`. These are exactly the contents of the lead's **exact** vector-force
  certificate `lead/FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md` §2 (C897's `μ_i > 0`, `ν_f > 0` with sum
  **exactly** `1`; every loaded edge has length `R*`; every anchor load has vanishing tangential component
  and strictly positive radial component `α(1 − c·U)/R* > 0`; dual work `= R*` hence `V(U*) = R*`), whose §1
  is the interval audit (`fresh_acute_slopes_interval.py`, mpmath.iv 50 digits; 11 face-vertex angle dot
  products `> 7/100`; the nine ties' `s_c, s_d` of opposite sign with `|·| > 51/100`). **Everything below is
  therefore conditional on C909**, and my earlier float export (40 positive / 11 zero, 19 values `< 1e−12`)
  drops to the role of a *consistency check* (see §3).

**Combinatorial premise (proved symbolically from `lead/FIXED-SWITCH-SOC-REDUCTION.md`).**
1. *Every ring site is anchored.* Each ring `c_i` owns the boundary interval `(U_{i−1}, U_i)`; its two
   endpoint constraints `|c_i − U_{i−1}| ≤ √t`, `|c_i − U_i| ≤ √t` are part of the 18 endpoint edges, and
   all 18 endpoint edges are **positive** (they are the defining switch contacts of the reduction). Hence
   every `c_i` is adjacent in `E⁺` to **two** anchors.
2. *Every face vertex is anchored.* The nine active faces (those carrying the cover; the slacked ones are
   the 6 excluded edges) contain each a hub: by the face-hub list of the same note, hub `9` appears with at
   least one active fan triangle and hub `10` likewise, and each of the nine active faces has all three of
   its incidence edges positive (C897 covers the two central faces `(c0,a,b)`, `(c4,a,b)`, so both hubs have
   a positive central face as well). Therefore every `z_f` is adjacent in `E⁺` to at least one ring site,
   which is itself anchored by (1).
3. *Consequence (corrected by the lead, 7e704215).* `E⁺` contains every ring→anchor endpoint edge and
   enough face edges to attach every **active** aux: the anchored part of `E⁺` consists of
   **11 sites + 9 active aux = 20 nodes**, and it is exactly those that are pinned. The remaining
   **2 slack aux** carry **zero force** and are **isolated** in `E⁺` — they are *not* claimed to be pinned
   (their movement does not change the value), and the lead's `C909`/`C910` proofs exclude them explicitly.
   So the correct statement is "the 20 force-carrying nodes lie in anchored `E⁺`-components", not "all 22
   free nodes" (my earlier 'all 22' was wrong); this holds **without consulting any numeric α**.

## 2. Lemma (uniqueness of the sites, no strict convexity used)

> **Lemma 1 (conditional on C909's exact force certificate).** Under (H1′)–(H2′), if `(X', t*)` is any other primal optimum at the same value `t* = R²`, then
> `X'_v − X'_w = X*_v − X*_w` for **every** edge `e = (v,w)`.

*Proof.* Fix `e`. The dual bound is
`p_e·(X'_v − X'_w) ≤ |p_e|·|X'_v − X'_w| ≤ |p_e|·R`.
Summing with the divergence-free relation (`lead/FIXED-SWITCH-SOC-REDUCTION.md` §3) and using
`Σ_e|p_e| = 1` and primal-dual equality `Σ_e p_e·(X'_v − X'_w) = t* = R` gives that **both** inequalities are
equalities for every `e` with `p_e ≠ 0` (a non-negative combination of non-positive slacks summing to `0`).
Hence `|X'_v − X'_w| = R` **and** `X'_v − X'_w` is parallel to `p_e` with the same orientation
(Cauchy–Schwarz equality case, legitimate because `p_e ≠ 0`). Therefore `X'_v − X'_w = R·p_e/|p_e|`, the same
vector as at the candidate. ∎

*No strict convexity of the objective, and no uniqueness of a maximiser, is used* (the lead's warning):
the conclusion is a **pinning of edge vectors** by the duals, not a convexity statement.

> **Corollary 2 (pinning propagates along `E⁺`).** Let `G⁺` be the graph on (anchors ∪ free nodes) with
> edge set `E⁺` (the active edges of (H1′); it is *not* the whole 51-edge set). Any free node `v`
> whose `G⁺`-component contains an anchor has its position **determined** by `U` and the pinned edge vectors:
> following a path from that anchor, the position is the anchor plus the sum of the pinned edge vectors.
> Consequently **all sites in anchored components are unique**; only nodes not reachable from any anchor
> (if any) may move, and such nodes are slack auxiliary nodes whose movement does not change the value.

## 3. Cross-check on the exported data (optional; not a premise)

`cline2-r23-gluing` exported the oracle dual (`r20-gluing/r20_fixed_u_dual_export.json`, schema
`{anchors, nodes, edges}`). Running this directory's calibrated checker on it:

```
nodes 22 ; anchors 9 ; positive edges 40 ; components 1 (contains all 9 anchors)
unpinned nodes 0 ; UNPINNED SITES: none   ->  PASS on the supplied floats
```

This agrees with the symbolic premise of §1 (all sites anchored). Two honest caveats, both from that
export: (i) it lists 40 positive edges with **11 zeros**, i.e. the slacked set as *stored* is larger than
the 6-edge bookkeeping — the symbolic §1 argument is therefore the load-bearing one, the check is only a
consistency test; (ii) 19 of the 40 positive values are `< 1e-12` (smallest `2^-54`), so the *numerical*
anchoring of `c1,c2,c3,c9,c10` is threshold-sensitive (`τ = 1e-14` already loses `c1,c10`). That concerns
the *quantitative* margin of (H1′) and the neighbourhood statement, **not** the symbolic combinatorial
premise; a certified (interval) dual or an exact active-set argument is needed before quoting a uniform
strict-positivity margin.

## 4. Compactness corollary (boundedness via the FULL 51-edge graph, not via `E⁺`)

> **Corollary 3 (conditional on C909, as above).** Let `U_n → U*` and let `X_n` be fixed-`U_n` optima with the same squared value `t*`.
> Then the sites of `X_n` converge to the sites of `X*`; all free nodes are **bounded uniformly**: every
> free node is connected to an anchor by *some* edge of the **full 51-edge graph** (zero-force/slacked edges
> included), and along such a path each step has length `≤ √t* = R`, hence
> `|X_v| ≤ max_i |U_i| + (path length)·R < ∞`. *(Corrected: boundedness does **not** need `E⁺` to be
> connected — slack aux nodes are bounded by their distance constraints even when their dual force is 0.
> Only the pinning/uniqueness uses `E⁺`.)*

*Cross-reference.* The lead's `FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md` §3 draws the same conclusion
(all eleven site coordinates pinned at fixed `U*`, `t ≤ R*`; the two slack aux may be non-unique and are
irrelevant) and §4 proves the stronger statement: for every site neighbourhood `O` there is an anchor
neighbourhood `N` such that **every** oracle-feasible solution with `U ∈ N` and `t ≤ R*` has its sites in
`O` — stronger than solver continuity. My Lemma 1 / Cor 2 / Cor 3 are therefore a *re-derivation of the
same step under the same certificate*; where they differ in strength the lead's §3/§4 govern.

*Proof.* Feasibility of `(X_n, t*)` gives `|X_n,v − X_n,w|² ≤ t*` for **all** 51 edges, so the full-graph
path bound applies; the feasible set at `t*` is closed and bounded, hence compact. A convergent
subsequence has a limit `(X', t*)` feasible for `U*` (continuity in `U`). By Lemma 1 applied on `E⁺`, the
edge vectors of `X'` on `E⁺` are pinned to those of `X*`; by the symbolic premise of §1 every site is in an
anchored `E⁺`-component, so the sites of `X'` coincide with `C*` (the 9 active aux are pinned too; the 2 slack aux are
irrelevant to the sites and to the value). Every subsequence has the same limit
(uniqueness of the pinned site positions), hence convergence. ∎

**Use (gluing interface).** Lemma 1 + Corollary 3 give exactly what the local primal-cover argument needs:
the *sites* (hence the covering disks) are locally unique and depend continuously on `U`, so the local
analysis at `U*` can be carried out on the single candidate configuration rather than on a family — with
the strict-positivity check (§3) and the non-degeneracy (H2) as the only remaining data obligations.

**Non-claims (aligned with C909).**
* All statements of §2/§4 are **conditional on C909's exact force certificate**
  (`lead/FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md` §2, with §1's interval audit) — given that certificate,
  "fixed `U*` ⟹ sites = `C*`" is a **theorem**, not a float reading; without it, the same sentence would be
  only a reading.
* My float export and the reachability checker are **consistency checks only**; the combinatorial premise
  of §1 remains symbolic and data-independent.
* No claim about dual uniqueness, about C902's own content, or about C897's proof (cited as a dependency);
  no novelty claim; nothing registered.
