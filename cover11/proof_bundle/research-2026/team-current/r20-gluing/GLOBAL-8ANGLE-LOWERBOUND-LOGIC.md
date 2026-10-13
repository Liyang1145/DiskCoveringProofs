# GLOBAL-8ANGLE-LOWERBOUND-LOGIC — placement uniqueness, canonicalization, Lipschitz/interval-dual BB interface

**Lane**: r20-gluing (cline2-r23-gluing). Read-only audit; **no claim registered**. Unified with
`lead/FIXED-SWITCH-SOC-REDUCTION.md` (same graph, same oracle, same α-formula). Per the lead the stress
lane owns the exact-root lift (interval acuteness & split), so **no numeric node-balance work here**.
Evidence: `q0_67_orbit_check.py`, `GRAPH-INTERFACE-CHECK.md`, `SOCP-DUAL-EXACT-FORM.md`,
claims C809/C818/C819/C824/C891/C892/C897/C249.

## 1. The surviving class is one labelled configuration up to symmetry — YES

Derivation: in the q0 core every face contains a hub and every boundary edge lies in exactly one face,
so the nine ring edges split into two contiguous chains `m_A + m_B = 9` with hub degrees
`m_A + 2, m_B + 2`; degrees `(6,7)` ⇒ `{m_A,m_B} = {4,5}`. Placements are `(u, u+4)`/`(u, u+5)` with
either chain assignment ⇒ **18 configurations**; under `D_9 × hub-exchange` they form **exactly one
orbit** (my enumeration, `q0_67_orbit_check.py`). Canonical representative: `u = 0`, `v = 4`, one hub
fanning the 4 edges `(0,1),(1,2),(2,3),(3,4)` and the other the 5 edges `(4,5)…(8,0)`, central faces
`(c0,a,b)`, `(c4,a,b)` — exactly the labelling of `FIXED-SWITCH-SOC-REDUCTION.md` §1 and the saved
candidate's faces `(0,9,10)`, `(4,9,10)`. So cyclic relabeling + hub exchange is a WLOG, not a
restriction.

## 2. Canonicalization and the exact angular domain (compact polytope)

For every true cover in this class with radius `r ≤ 19/50`: rotate/reflect/exchange hubs to the
canonical labelling; its switches `U_0..U_8 ∈ ∂D` (nearest-cell switches, **not** centre-angle
bisectors) then satisfy the polytope constraints of `FIXED-SWITCH-SOC-REDUCTION.md` §4:
* each owned interval has width `Δ_i ≤ L = 2asin(19/50)` (the whole owned interval lies in one short
  arc; the endpoint chord inequality alone would not exclude a major arc),
* `ΣΔ_i = 2π` ⇒ `Δ_i ≥ m = 2π − 8L > 0` (positivity exact since `19/50 < sin(π/8)`),
so, modulo rotation (fix `U_0 = (1,0)`), the true switch lists live in the **compact 8-dimensional
polytope** `P = {Δ ∈ [m, L]^9 : ΣΔ = 2π}` — **not** the whole 8-torus, and not all of `(S¹)^9`.
The cover itself is a feasible point of the fixed-switch oracle at its own `U` (sites = its sites,
`z_f` = its interior primal Voronoi vertices) ⇒ `V(U) ≤ r`. Only the direction **cover ⇒ feasible** is
used; no "oracle feasible ⇒ cover" is needed. (No hub-to-switch constraints: interior hub disks cover
no boundary point.)

## 3. Analytic Lipschitz bound for `V` (replaces "the only numeric work is a BB")

**Lemma.** For unit anchors `U, W` with the **same** face structure,
`|V(U) − V(W)| ≤ ε := max_i |U_i − W_i|`.
*Proof.* If `(C, Z, t)` is feasible at `U`, then at `W` every endpoint constraint still holds with `t+ε`
(`|c_i − W_i| ≤ |c_i − U_i| + |U_i − W_i| ≤ t + ε`, likewise for `W_{i−1}`), and the 33 face
constraints are unchanged (they involve no anchor). So `(C, Z, t+ε)` is feasible at `W`, i.e.
`V(W) ≤ V(U) + ε`; symmetrically. ∎
Consequences: `V` is 1-Lipschitz in the max-norm on anchor positions (analytic; no acuteness, no grid,
no dual construction needed). **Correction (lead):** evaluated at the sharp anchor it gives only
`V(W) ≥ V(U*) − ε = R* − ε`, i.e. a bound *below* `R*` — it does **not** certify `min_P V ≥ R*` on any
neighbourhood of `U*`, and I withdraw that phrasing. Its correct uses: (i) bounding how fast `V` may
deviate, (ii) turning a certified value at `W` into a bound on an ε-ball around `W`, and (iii) sizing
boxes. Sharpness instead needs a *varying* dual or the local theorem of §5.
(`FIXED-SWITCH-SOC-REDUCTION.md` §3 adds the complementary structural facts: the force set is compact
and anchor-independent, so `V` is convex and positively homogeneous in **Cartesian** anchor coordinates
and rigid-motion invariant — convexity does **not** extend to the angular domain, which is why this
polytope/Lipschitz route is the sound one.)

## 4. Interval-dual bound over an 8-angle box (sound BB kernel interface)

Take any dual-feasible force field `p_e` (divergence 0 at every free node, `Σ_e |p_e| ≤ 1`) — it is
**independent of `U`** (lead note §3). Its certificate reads `V(U) ≥ Σ_i l_i·U_i` with `l_i` the signed
anchor sum. On a box `B` of anchor positions the bound `min_{U ∈ B} Σ_i l_i·U_i` is **separable in the
absolute angles**: for one anchor with `l ≠ 0`, `φ = arg l`, and the box's conservative angular
interval `[θ_lo, θ_hi]` (interval hull), the minimiser of `⟨l, U(θ)⟩` is at `θ = φ + π (mod 2π)`
(**corrected**: `φ` itself is the *maximiser*, not the minimiser), so
```
min_{θ ∈ [θ_lo,θ_hi]} ⟨l, (cos θ, sin θ)⟩ = −|l|      if φ + π ∈ [θ_lo, θ_hi] (mod 2π),
                                           = |l| · min(cos(θ_lo−φ), cos(θ_hi−φ))   otherwise,
```
the **cos endpoint / critical-point rule** — no grid, no sampling. For correlated width boxes
(`ΣΔ = 2π`, `Δ_j ∈ [lo_j, hi_j]`) use the interval hull of each cumulative angle
`θ_i ∈ [θ_0 + Σ_{j<i} lo_j, θ_0 + Σ_{j<i} hi_j]` (conservative ⇒ sound, possibly weaker than an exact
polytope-aware bound). Summing the nine separable minima gives a certified lower bound for `V` on the
whole box; a finite cover of `P` by such boxes yields a global lower bound if every box bound is `≥ R*`.
Note the fields may be chosen **per box** (they need not be optimal at `U*`), which is exactly what §5
shows is necessary.

## 4′. Conditional finite-dual obstruction — finite fields cannot be sharp near `U*`

**Lemma (conditional; only the stated hypotheses are used).** Fix the face structure and the sharp
anchor tuple `U*`. Suppose **every** dual-optimal field `p` at `U*` (i.e. `bound(U*;p) = V(U*) = R*`)
has **purely radial anchor loads** `l_i(p) = β_i(p) U*_i` with `β_i(p) ≥ 0`, `Σ_i β_i(p) = R* > 0`, and
suppose the support sees every admissible shape perturbation, i.e.
**(H-supp)** for every anchor tuple `W ≠ U*` that is not a common rotation of `U*`, some `i` with
`β_i > 0` has `W_i ≠ U*_i` (automatic if `β_i > 0` on all nine anchors). Then for every `W ≠ U*` and
every optimal `p`,
```
bound(W; p) = Σ_i β_i ⟨U*_i, W_i⟩ = Σ_i β_i cos δθ_i  <  Σ_i β_i = R* ,
```
strictly, because `cos δθ_i ≤ 1` with equality only at `δθ_i = 0` and (H-supp) forces at least one
strictly positive `β_i` to have `δθ_i ≠ 0`. **Consequences.**
1. Each *attaining* optimal field has a **strict** maximum `R*` exactly at `U*` (rotations included:
   `Σβ_i cos γ < R*` for `γ ≠ 0`).
2. Each *non-attaining* field has `bound(U*; p) < R*` and, being continuous (linear in `W`), stays
   `< R*` on a neighbourhood of `U*`.
3. Hence for **any finite set of dual fields** `p_1,…,p_N`,
   `max_j bound(W; p_j) < R*` for all `W ≠ U*` in the domain (localised to a punctured neighbourhood if
   (H-supp) only holds locally). So **no finite family of U-independent dual fields can certify
   `min_P V ≥ R*` at `U*`**; a sharp certificate needs a **U-dependent (varying) dual**, or the
   quadratic/local route below, or a per-box field family.
4. Second-order picture (why the obstruction is quantitative): near `δθ = 0` the fixed field gives
   `R* − ½Σ_i β_i δθ_i² + O(δθ⁴)` while the Lipschitz bound gives `R* − ε`; both lie below `R*`, and
   the two coincide in order only when `ε ≍ Σβ_iδθ_i²`.
**Caveats.** The lemma is *conditional*: it is **not** asserted that the candidate's optimal duals are
radial-positive (that premise is the stress lane's C897-lift obligation), nor that the optimal dual is
unique, nor that non-optimal fields are unique or isolated. If some optimal field has a tangential
(non-radial) component, points 1–3 can fail and the obstruction does not apply. If some `β_i = 0`
while that anchor's angle is the only one changing (a shape change invisible to the support), (H-supp)
fails and the bound can remain `R*`.


## 5. Conditional main theorem (threshold corrected)

Let `R*` be the **C891 exact-root radius** — the radius of the exact candidate root, whose cover is
certified by `C892`; `R*` is **not** the 45-digit printed value of C249 and **not** the C529 rational
`3799838531198387090485182/10^25`. Only `C892`'s exact-root cover supplies the matching upper bound
`≤ R*`; a rational upper bound strictly larger than `R*` cannot sandwich equality with a lower bound
`R*`.

> **Theorem (conditional).** Assume
> **(H1)** the 9+2 reduction and the classification chain `C809 → C818 → C819 → C824` (every
> eleven-disk cover with `R ≤ 19/50` lies, up to relabelling, in the surviving q0(6,7) class);
> **(H2)** §1–§2 (placement uniqueness; canonicalization; the compact polytope `P` of switch widths);
> **(H3)** a certified lower bound `min_{U ∈ P} V(U) ≥ R*` — by a finite cover of `P` with the §4
> per-box dual bounds (fields chosen per box), or by a **varying-dual / local** argument at the sharp
> anchor `U*` (a single U-independent field cannot do it — §4′); the Lipschitz bound of §3 alone gives
> only `R* − ε` there.
> **(H4)** `C892` (the exact-root cover with radius `R*`).
> **Then** `r_D(11) = R*`.

**Scope caveats.** (i) `V(U*) = R*` at the candidate's anchor is the *local* sharpness content of the
C897 lift (lead note §5); it does not by itself give `min_P V ≥ R*` — the outer 8-angle problem
remains, and by §4′ finite U-independent dual fields cannot close it near `U*` under the radial-load
hypothesis. (ii) If the oracle is strictly below `R*` at some distant `Δ ∈ P`, that disproves only this
relaxation inequality, not covering optimality; the fix is to add a necessary condition there
(arc-interior coverage, hub strictness, the two slack faces, or a new cut). (iii) The exact
acuteness/slope interval premises at the C891 root are checked by the stress lane, not here.
(iv) C907's joint-hub convexity in a nominal ring box neither identifies `U*` nor certifies the full
candidate lift. (v) §4′ is *conditional*: the radial-positive-load premise on the optimal duals is not
assumed, and uniqueness/isolation of duals is not assumed.

**Repro / evidence**: `q0_67_orbit_check.py` (orbit enumeration); this note is otherwise analytic.
Sharpness at `U*` via the primal route (*local feasible ⇒ cover*) is developed in
`LOCAL-PRIMAL-TO-COVER-TRANSFER.md` (L1 no-hole, L2 endpoint ⇒ arc, L3 MEC = Rc for acute faces;
interfaces I1–I10). Direction discipline: dual fields give `V ≥ bound` only — a small bound never
implies `V` is small, so the local theorem has to come from the primal side.
