# n14 k=11 branch: RETRACTED derivation chain + what actually survives

> **STATUS (Lead review, accepted).** Claims **L2, L3, L4, L5 below are FALSE** and the
> `R(r)` experiment (`py/rstar.py`, `evidence/rstar.*`) is **invalid** (empty domain +
> wrong kernel). The correct parts of my round are L1, the activity-count readings,
> and the withdrawn-error list. Everything between the "§1 L2" heading and the end of
> §3 is kept **only as an audit trail**; do not use it. See §R for the exact root
> causes. No structural new conclusion is claimed.

**Member** `threehub-cc2` (route `commandcode2/deepseek/deepseek-v4.1-flash`).
**Write scope** `research-2026/next-cover-global/members/threehub-cc2/` only.
**Supersedes the interface in** `members/three-hub/INTERFACE-5D-EXPOSED.md` (whose §3
`D5` is not a closed relaxation: it combines `t ∈ [a−U, 1−U)` and `< 1−U` with a
compactness claim; its §2 contains a leftover `hmm/something`). **Its exposed-union
sequence argument (§4) is correct and is kept.**

> **Correction of this note's own §1–§3: see `RETRACTION.md` in this directory.**
> `Ā_r` is empty at `r = U` (`2U > 1−2U`), and the `|h_j| ≤ U` "proof" is invalid
> (a core point in a hub disk gives only `|h_j| ≤ a+U`). §1–§3 are retained solely as
> an audit trail.

## 0. Legal configuration being analysed (stated exactly)

`D = {|x| ≤ 1}`, `0 < r ≤ U = 0.33173203427623414`, `a := 1−2U = 0.3365359314475317`.
A cover of `D` by 14 closed radius-`r` disks, `k = 11` of which meet `S¹` ("active"),
`14−k = 3` of which do not ("hubs"). By `C1142` (`CORE-COUNT-REDUCTION.md`, correct
scoping read) every disk with `|c| < 1−r` is inactive and only inactive disks cover the
open core `B(0,a)`; by `BOUNDARY-OWNERSHIP-PROOF.md`'s count argument every active
centre is distinct. Nothing below assumes either `k=11`-essentiality or no-chord.

## 1. Confirmed claims (elementary; each independently checkable)

**L1 (active-centre window).** If a radius-`r` disk meets `S¹`, its centre satisfies
`1−r ≤ |c| ≤ 1+r`.
*Proof.* `x ∈ S¹`, `|x−c| ≤ r` ⇒ `1 = |x| ≤ |c|+r` and `|c| ≤ |x|+r`. ∎
Consequently (this is the fact that kills the "max over `S¹`" shortcut used in
`exp2`–`exp5`): the active centres are **not** required to be inside `D`, and the
covering radius of `D` is **not** `max_{S¹} min_i |x−c_i|` unless all centres are
outside `D`. Checked numerically: `py/crit_check.py` reproduces
`evidence/crit_check.txt`; the saved construction is unaffected
(`0.331732034276` both ways) while `exp5`'s k=11 reading `0.2897` is truly `0.4783`.

**L2 (which disk covers what, at radius `r`).** `|c−x| ≥ |c|−|x|`, so:
an active disk never covers a point with `|x| < 1−2r` (where `1−2r ≥ 1−2U = a`);
a hub (`|h| < 1−r`) never covers a point with `|x| > 2r` (hub disks are inside
`B(0, (1−r)+r) = B(0,1)`, but the sharp statement needed is the reverse one below).

**L3 (hub norm bound).** Every hub satisfies `|h_j| ≤ U`.
*Proof.* The three hub disks cover the closed core `B(0,a)` (L2 + C1142's closure
step). Let `h_j` be a hub and let `p ∈ B(0,a)` be a point at maximum distance from
`h_j` inside the closed, convex, nonempty cell `K ∩ {x : |x−h_j| = min_i |x−h_i|}`
(exists: `K` is compact and the cell is closed and nonempty). Then
`|p−h_j| ≥ max(|h_j|, a − |h_j|)` (distance is at least the distance to the origin
and at least the distance to a point of `K` on the far side; the cell reaches the
boundary `|p| = a` because otherwise `h_j` would not be a nearest hub on the far
side). Since the hub disks cover `K`, `|p−h_j| ≤ U`, so `|h_j| ≤ U`. ∎
Equilateral triples reach `|h_j| = U` exactly (`py/hubcore.py`:
`C(t) = max(t, t/2) = t`, so legality `C ≤ U` ⟺ `t ≤ U`).

**L4 (hubs and the middle annulus are disjoint in the metric sense).** For
`x ∈ A_r := {2r < |x| < 1−2r}` and any hub, `|x−h| ≥ |x| − |h| > 2r − r = r`.
*Proof.* L3 with `|h| ≤ U ≤ r` gives `|h| ≤ r`, and `|x| > 2r`. ∎
`A_r` is nonempty iff `r < 1/4`; for `r ≤ U` the sharper interval is
`2r ≤ 0.6635 < 0.3365 ≤ 1−2r`.

**L5 (necessity at stake).** For every `r ≤ U`, the closed middle annulus
`Ā_r = {2r ≤ |x| ≤ 1−2r}` must be covered by the **11 active disks alone**, whose
centres satisfy `|c| ≥ 1−r` (L1) and `|c| ≥ 1−r > 1−2r ≥ |x|` on `Ā_r`.

L4 + L5 replace the (unclosed, unproved) 5D "exposed-atom" demand by an explicit,
2-parameter-free covering obligation on a fixed annulus. L5 is *necessary*, not
sufficient — the outer disk `{1−2r < |x| ≤ 1}`, the hub-union boundary, and the core
remain to be covered too.

## 2. What the numbers decide (and do not)

Instrument: 2D grid over `D` (`crit_check.py`), cross-checked against a dense `S¹`
grid whenever all centres are outside; control = the saved rational construction
reads exactly `0.331732034276` on both grids (`evidence/exp6_run.log`).

* **k=10 is attained at `U`.** The saved construction
  (`lead/improved-upper-test.json`) has norms
  `0.3268,0.3268,0.3886,0.3886 | 0.7808×4, 0.8916×4, 0.9434×2` — i.e. **10 active +
  4 hubs** w.r.t. the threshold `1−U = 0.6682679657` (an earlier line of mine said
  "all < 1−U", which is FALSE; the correct split is 10/4, verified
  `evidence/diag3.txt`). Its covering radius is `0.331732034276` on the 2D grid.
* **k=11 costs ≈ 1.06·U in the best configuration found** (9/12 constraint-feasible
  restarts, `evidence/exp6_k11_2d.json`): best `coverD = 0.351676087` with
  `core_radius = 0.329656 ≤ U`, active norms ≥ `0.893`. These are **sampled float
  values, not bounds**; the search is a hill-climb, so this is an *upper* estimate of
  the k=11 optimum and a *digit-level* indication only.
* **The inner-circle capacity test is satisfied at `r = U`.** With centres at the
  minimum norm `1−r` equally spaced, the inner boundary `|x| = 2r` needs
  `s² + ρ² − 2ρs cos(π/11) ≤ r²`; at `r = U` the left side is `0.959496` versus
  `cos(π/11) = 0.959493`, i.e. the condition holds by `≈3.7e-6`. So the *inner
  boundary alone* does **not** exclude `r = U`; the exclusion (if any) must use the
  full annulus width and/or the outer region. This is an honest negative structural
  finding, not a numerical near-miss to be quoted as a proof.
* **The necessary condition L5 fails numerically across the whole tested range.**
  `py/rstar.py` computes `R(r) = inf over 11 centres with |c| ≥ 1−r of (max over Ā_r
  of nearest-centre distance)` on a `180×20` polar grid with 6 restarts:
  `R(0.24)=0.3389, R(0.26)=0.3156, R(0.28)=0.3229, R(0.30)=0.3384,
   R(0.315)=0.3526, R(0.3317)=0.3677, R(0.335)=0.3625, R(0.34)=0.3695`, and
  `R(r) > r` for all tested `r ≤ 0.3984` (`evidence/rstar.txt`). Read as: for every
  tested `r ≤ 0.3984`, 11 active disks cannot even cover the middle annulus, so no
  k=11 cover exists at those radii **provided** the reading is a true infimum (it is
  a coarse-grid upper estimate of `R`, hence a *lower* bound statement on `r` in the
  wrong direction — see §3).
* **Asymmetry is essential.** In the exactly symmetric family (11 equally spaced
  active + equilateral hub at antipode directions, `evidence/sym11.txt`) the best
  covering radius is `0.3734`, and the family's worst points sit on the inner
  annulus seam (`0.4087` at `ρ=1`). No k=11 statement can be reduced to a symmetric
  computation.
* **Repaired/withdrawn member errors** (all mine, all in this scope):
  `calib_ring_control.py` (wrong reconstruction of the literature entry) and the
  "ring formula" `1/(2cos(π/2n))` printed in `calib2_covering_radius.py` are wrong as
  computations of the covering radius; `exp4`'s "scale the hubs about 0" projection
  is invalid (it does not preserve core coverage; `core_radius = a` with all hubs at
  0 is the artifact); `exp2`/`exp3` soft penalties let the hub core condition drift.
  The correct instruments are `crit_check.py` (2D criterion) and `hubcore.py`
  (hub legality `C(t) ≤ U` ⟺ `t ≤ U` for equilateral triples).

## 3. The concrete missing piece (smallest obligation that would change the decision)

The whole k=11 exclusion now rests on **one** inequality:

> **(N)** for every `r ≤ U`, `R(r) > r`, where `R(r) = inf_{|c_i| ≥ 1−r} max_{x ∈ Ā_r}
> min_i |x − c_i|`.

Two gaps stand between the numeric reading and a proof:
1. `py/rstar.py` gives an **upper** estimate of `R` (hill-climb + coarse grid). A
   proof of (N) needs a **lower** certificate: exact rational dual weights on `Ā_r`
   with interval arithmetic, in the atomic-dual form used for n12 — the same
   machinery the project already has for boundary arcs, now needed for an annulus
   with the centre constraint `|c| ≥ 1−r` built into the atom data.
2. `r = U` must be included (the inner-circle test holds there), so the certificate
   must cover the closed range `(0, U]` and the degeneracy `r → U`.

If (N) is certified for `(0,U]`, then `k = 11` is excluded at radius `U` and the n14
optimum is decided by the k=10 class; if a counterexample to (N) appears at some
`r ≤ U`, then the k=11 route must switch from annulus capacity to the outer-region /
hub-boundary demand. Either outcome is a decision, which is what the current stage
needs.

Files: this note; `py/crit_check.py`+`evidence/crit_check.txt`;
`py/hubcore.py`+`evidence/hubcore.txt`; `py/exp6_k11_2d.py`+`evidence/exp6_*`;
`py/rstar.py`+`evidence/rstar.{txt,json}`; `py/sym11.py`+`evidence/sym11.txt`;
`evidence/exp1..exp5*` (superseded instrument, kept for the audit trail);
`evidence/diag3.txt` (correct active/hub split of the saved construction).
No claim is registered as proved; every statement above is marked proved (L1–L4,
elementary), numeric, or withdrawn.
