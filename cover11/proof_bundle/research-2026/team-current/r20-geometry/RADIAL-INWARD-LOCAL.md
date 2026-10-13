# Radial inward move of a ring: exact dominance, obstruction criterion, and the tie-tightening test

Author: r20-geometry (cline2 route; lead-directed bounded action; no subagents, no claim registered).
Evidence: `radial_inward_local.py/.out.txt/.json`, `radial_tightening.py/.out.txt/.json`.
Scope: local 2-ring+hub read, instantiated on the certified q0(6,7) centres; **no grid, no optimisation**.

**Chinese scope line.** 问题（lead）：9 个 ring inward roots 弧实际重叠时，能否逐个 radial inward 直到某
boundary tie tight 而**不丢整 D 覆盖**？结论（有界）：①精确单环 dominance 判据：`B(c,r)∩D ⊆ B(tc,r) ⟺
t ≥ (1−r²)/s²`（`s=|c|>1−r`）；`t=(1−r²)/s²` 处正是 C464 的内根 `ρ₋=(1−r²)/ρ₊`，故 C464 = 本判据的端点；
②在 inner-root 级别以下（`s<sqrt(1−r²)`）内移会丢掉"外侧月牙" `S(c)={x∈∂B(c,r)∩D: x·c>s²}`；若 `S(c)`
中有点不被其他盘严格覆盖，则该环**任何**内移都破坏覆盖（这就是要找的局部反例形态）；
③有限移动判据：`t_fail(i)=max_{x∈Q_i} t₋(x)`（`Q_i`=只被该环覆盖的点集），`t_bdy(i)`=私有边界弧端点的同
一函数值；`t_fail ≤ t_bdy` ⟹ 内移恰好可达 tie 饱和，`t_fail > t_bdy` ⟹ 覆盖先破（内部见证）。
④实例（certified 9-ring 中心，`r=r*` 与放大到 0.40/0.43/0.50/0.55 的真覆盖；`r>r*` 时弧真实重叠
2.6°–12.8°）：**每一环的绑定点都在 ∂D 上**（`|x*|=1−5e-10`，`t_fail=t_bdy` 到 1e-9）⟹ 在该族里
radial inward 可以一直做到某个 boundary tie 变紧，且整 D 覆盖不丢（lead 的"删 slack"在本族可行）；
**未找到**真覆盖反例。保留项：`∂B(c_k,r)∩cl Q_i` 弧上的驻点类未枚举；迭代到全 tie 饱和未做。

## 1. Exact one-ring geometry (dominance criterion and the lost sliver)

**Domain (lead's correction, team-message-3f429db4).** "Inward radial" means the ring centre norm
satisfies `ρ ≤ √(1−r²)`, **not** `|endpoint| = 1`. This is exactly the threshold below: at an outer
root `s = ρ₊ ≥ √(1−r²)` the inward-canonical representative of the same boundary arc is C464's inner
root `ρ₋ = (1−r²)/ρ₊ ≤ √(1−r²)`; `|endpoint| = 1` is the *outer* end of the root pair. (The pair
"inner pin" `p_in` is a different object: a point of the plane — the inner circle–circle intersection
of two ring circles — not a centre norm; §2–§3 of `STRICT-HUB-FINITE-DISJUNCTION.md` use it as a disk
centre, never as the radial representative.) Domain flags of the tested rows
(`radial_span_check.out.txt` Part 1): all nine rings satisfy `s ≤ √(1−r²)` for
`r ∈ {r*, 0.39, 0.40, 0.43, 0.45}`; at `r = 0.50` ring 1 leaves the domain, at `r = 0.55` rings
1,7,8 do (those rows are generic-cover readings only, not inward-canonical ones).

Ring centre `c`, `s=|c| ∈ [1−r, 1]`, disk radius `r`, `e=c/s`, unit disk `D`. Move `c → tc` (`t ≤ 1`).
For a point `x` with `|x−c| = r`:

$$|x-tc|^2-r^2=(1-t)\bigl[2\,x\cdot c-(1+t)s^2\bigr],\qquad
\max_{x\in B(c,r)\cap D}x\cdot e=\min\Bigl(s+r,\ \frac{1+s^2-r^2}{2s}\Bigr).$$

Hence, for `s+r > 1` (every essential ring: the disk crosses `∂D`),

> **`B(c,r) ∩ D ⊆ B(tc,r)`  ⟺  `t ≥ (1−r²)/s²`  (dominance), for `0 < t < 1`.**

**Domain reading (lead's correction, do not reverse it).** The criterion is valid on `0<t<1` and in
the boundary-crossing case `s+r>1` only.
* If `s² < 1−r²` (the inward-root regime, all nine certified rings at `r*`) the right-hand side is
  `(1−r²)/s² > 1`, so **no nontrivial radial dominance exists** — the move always loses the outer
  sliver below. It must **not** be read backwards as "dominance for small `t`".
* If `s+r ≤ 1` (disk entirely inside `D`) the criterion reads `t ≥ 1 + 2r/s > 1`, i.e. again dominance
  only at `t = 1` (an inward move loses the disk's far cap).
* At an **outer root** `s = ρ₊ ≥ √(1−r²)` the endpoint `t = (1−r²)/s²` is exactly C464's inner root
  `ρ₋ = (1−r²)/ρ₊`: C464 is the endpoint case of this criterion.
(`s < √(1−r²)`, which holds for all nine certified rings at `r*`: `|c| ≤ 0.8925 < √(1−r*²) = 0.9250`)
the lost set `B(c,r)\B(tc,r) ∩ D` is nonempty and shrinks, as `t→1⁻`, to the **outer sliver**

$$S(c)=\{\,x\in\partial B(c,r)\cap D:\ x\cdot c>s^2\,\}
=\{x=c+r(\cos\beta,\sin\beta):\ \beta_{\rm end}\le|\beta|<\pi/2\},\qquad
\beta_{\rm end}=\arccos\frac{1-s^2-r^2}{2rs},$$

two arcs on the ring's own circle, adjacent to its arc ends (nonempty iff `s < √(1−r²)`).

## 2. Obstruction criterion (the shape a genuine local counterexample must have)

If `x ∈ S(c)` is not **strictly** covered by any other disk (`|x−c_k| > r` for all `k ≠ i`, or weakly
covered with an outward escape direction available), then for **every** `t < 1` the point `x` (or an
arbitrarily close point) leaves `B(tc,r)` and is not covered elsewhere: **no inward radial move of
ring i preserves the cover.** This is the exact local failure mode to look for in the 2-ring+hub
model (the "genuine covered counterexample" of the lead's instruction). On the certified centres at
`r ∈ {r*, 0.39, 0.40, 0.43, 0.45}` the sliver is **covered** by the other ten disks for all nine
rings (`radial_inward_local.out.txt`), so no such immediate obstruction exists in this family.

## 3. Finite-move test: does the move reach a TIGHT tie before the cover breaks?

Write `Q_i = {x ∈ D : |x−c_k| > r ∀k≠i}` (points only ring i can cover; nonempty since ring i is
essential). For `x ∈ Q_i` the feasible `t`-set is the interval `[t_-(x), t_+(x)]` with

$$t_-(x)=\frac{p-\sqrt{p^2-s^2(q-r^2)}}{s^2},\qquad p=x\cdot c_i,\ q=|x|^2 .$$

The cover after moving ring i to `tc_i` holds iff no point of `Q_i` is outside `B(tc_i,r)`, i.e. iff
`t ≥ t_fail(i) := max_{x∈Q_i} t_-(x)`. Let `t_bdy(i)` be the same function evaluated at the endpoints
of ring i's **private boundary arc** (the part of `∂D` covered only by ring i). At `t = t_bdy` that
endpoint is at distance exactly `r` from the moved ring while its neighbour is at distance exactly
`r` too: **the boundary tie is tight (the two arcs are head-to-tail)**. Therefore

> `t_fail ≤ t_bdy` ⟹ the inward move can be continued exactly until a tight tie (cover intact);
> `t_fail > t_bdy` ⟹ the cover breaks at an **interior** point strictly before any tie tightens.

`t_fail` is evaluated on a **complete** finite candidate set, via the monotonicity lemma below;
`t_bdy` in closed form.

### 3.1 Monotonicity lemma (makes the candidate set complete)

With `x = λ(cos(θ_i+φ), sin(θ_i+φ))` in the ring's frame (`c_i = s(cosθ_i, sinθ_i)`),

$$t_-(x)=F(\lambda,\varphi)=\frac{\lambda\cos\varphi-\sqrt{r^2-\lambda^2\sin^2\varphi}}{s},\qquad
\frac{\partial F}{\partial\lambda}=\frac{\cos\varphi+\frac{\lambda\sin^2\varphi}{\sqrt{r^2-\lambda^2\sin^2\varphi}}}{s}>0
\ \ (\cos\varphi>0),$$
$$\frac{\partial F}{\partial\varphi}=\frac{\lambda\sin\varphi}{s}\Bigl[-1+\frac{\lambda\cos\varphi}{\sqrt{r^2-\lambda^2\sin^2\varphi}}\Bigr],
\qquad \text{sign}= \operatorname{sign}(\sin\varphi)\ \text{ for }\lambda>r .$$

So on the outward half (`cosφ>0`) `F` is **increasing in `λ`** and (for `λ>r`) **increasing in `|φ|`**;
on the inward half `F<0` (no constraint). Consequently `max_{cl Q_i}F` is attained either (i) at an
arrangement crossing of `cl Q_i` (arc endpoints: circle–circle or circle–`∂D` crossings), or (ii) at a
**Pareto point of `(λ,|φ|)`** on a boundary arc, i.e. `λ'=0` or `φ'=0`, which on a circle are the
closed-form points `c(1+r/|c|)` (farthest from the origin) and `x = c+rw`, `w·(c/|c|) = −r/|c|`
(radial tangency) — or, on a piece where `F ≡ 1` (the outward half-arc of ring i's own circle), at an
endpoint of that piece, which is again a crossing with the same value. `radial_tightening.py`
enumerates exactly this set (89 candidates at `r ≈ 0.4`).

*Remark (an earlier over-strong criterion, recorded for honesty):* the naive sufficient condition
"every point of `cl Q_i` has `|φ| ≤ φ_max` (angular span of the private boundary arc)" **fails** at
vertices for several certified rings (e.g. ring 6 at `r*`: `max|φ| = 0.544` vs `φ_max = 0.281`,
`radial_span_check.out.txt` Part 2) — those off-span vertices are *inward* (small `λ`), and by the
lemma they cannot bind. The Pareto form above is the correct (and proved) version.

## 4. Instantiation on the certified q0(6,7) geometry (the answer for this family)

The certified centres at `r = r*` are a genuine cover, and enlarging `r` keeps it (monotone), with
**genuinely overlapping arcs** for `r > r*`:

| r | arc overlaps at the nine seams (deg) | cover |
|---|---|---|
| `r* = 0.37998385…` | all exactly `0.00` (arcs tile: already saturated) | certified |
| 0.40 | 2.64, 2.64, 3.52, 3.85, 3.14, 2.90, 3.14, 3.85, 3.52 | by monotonicity |
| 0.43 | 6.59, 6.59, 8.54, 9.31, 7.74, 7.20, 7.74, 9.31, 8.54 | by monotonicity |
| 0.45 | 9.21, 9.21, 11.79, 12.81, 10.76, 10.04, 10.76, 12.81, 11.79 | by monotonicity |

Result of the finite-move test (all nine rings, all five radii; `radial_tightening.out.txt`):

* **Every binding witness lies on `∂D`** (`|x*| = 1 − 5·10⁻¹⁰`), its nearest disk is the adjacent
  ring (`+3.6·10⁻¹⁰ … +5.2·10⁻¹⁰` margin) and the hubs are far (`+0.33 … +0.53`) — so the first
  event is a **boundary tie saturation**, not an interior gap;
* `t_fail = t_bdy` to `~3·10⁻⁹` for every ring; sample values at `r = 0.40`: ring 1 `t = 0.8436722724`
  (seam with ring 8 at 110.83°, consuming the 2.64° overlap), ring 7 `0.8699766984`, ring 8
  `0.8699766981`, ring 9 `0.8886090871`, ring 4 `0.9165362925`, ring 6 `0.9394090913`; at
  `r = 0.55`: ring 1 `0.5213929947`, ring 7 `0.5424104145`, ring 6 `0.6460218067`;
* at `r = r*` the same computation gives `t_bdy = 1 − 4·10⁻¹⁵` for all nine rings (arcs already
  tight ⟹ no slack to delete), confirming the saturated status of the certified object.

**Verdict (bounded, for this family):** the radial inward move **can** remove the arc-overlap slack
one ring at a time until a boundary tie is tight, with the whole-`D` cover intact; no local
counterexample of the obstruction type (§2) exists on the tested family. This is evidence *for* a
possible saturation reduction on the certified geometry — not a proof for all configurations.

## 5. Open items / honest limits (before any expansion)

1. **Arc candidates closed, general configurations open.** With §3.1 the candidate set for
   `max_{cl Q_i} t_-` is complete, so for each *tested configuration* the statement "the first failure
   of the inward move is a tight boundary tie" is now proved (finite check + monotonicity), not merely
   sampled. What is *not* proved is the statement uniformly over the legal ring domain: that would
   need either an inequality `F(x) ≤ F(seam)` for all `x ∈ cl Q_i` from the ring hypotheses (a
   structural estimate on the private region), or an interval/evaluation certificate of the finite
   conditions over a box of ring parameters.
2. **Iteration**: the test moves *one* ring at a time. After saturating one seam the configuration
   changes; reaching all-saturated simultaneously requires an iteration/continuity argument (at each
   step the same finite test must be re-evaluated). Not done.
3. **No genuine covered counterexample was constructed.** §2 states exactly what it would need (an
   uncovered outer-sliver point, or an interior witness with `t_- > t_bdy`). The certified family
   supplies neither; a targeted search should look for rings whose outward sliver escapes their
   neighbours (e.g. a gap between consecutive ring centres approaching/exceeding `2r`, or a hub that
   fails to cover the waist).
4. **Relation to the boundary-arc ledger**: at `r = r*` the nine overlaps are exactly zero, i.e. the
   certified object is already in the saturated ("arcs head-to-tail") class; the present test is a
   statement about *other* legal configurations in the same graph, which is where a saturation WLOG
   would have to be justified.

## 6. Interface with the lead's fixed-endpoint counterexample, and the joint hub move

The lead's `FIXED-ENDPOINT-SATURATION-COUNTEREXAMPLE.md` (r=3/8, `H=(1/2,0)`, `c0=(q,0)`,
`c±=q(cos2A,±sin2A)`, `A=asin r`, `q=√(1−r²)=√55/8`) is **independently confirmed**
(`lead_counterexample_check.out.txt`): the arcs tile `[−3A,3A]` (half-width at radius `q` is exactly
`A`); `U±=(q,±r)` are `2r` apart, so the lens of the two radius-`r` disks through them is the
singleton `{c0}` — the internal centre is **forced** by gap coverage alone; and
`Rc² = 71/220 − 23√55/880 = 0.12889481226909062748 < r² = 9/64` (slack `+0.01173`; the rational
bracketing `√55 > 641/92` holds since `55·92² = 465520 > 641² = 410881`). In the `ε`-family the
lens `L_ε` obeys `|c−(cos g,0)|² ≤ r² − sin²g → 0`, so *every* bridging centre converges to `c0`
uniformly.

What this kills and what it does not:

* **Killed:** saturating either **fan** by moving the internal ring centre with hub and endpoints
  fixed. Correct conclusion; recorded in `DEAD.md`.
* **Not affected:** the **boundary-tie** radial criterion (§1–§3). The two notions differ already in
  the `ε`-family: at `ε=0` the middle ring's seam value is `t_bdy = 1` (no inward move at all, exactly
  the lead's "no movement feasible"), while for `ε>0` the seam value is `< 1` (e.g. `ε=10⁻³`:
  `t_bdy = 0.97303`) — the middle ring *can* move inward until its boundary tie with a neighbour
  saturates, while the fans stay slack for every bridging centre. Fan slack and arc-overlap slack are
  independent parameters.
* **The joint move the lead asks for works — on the hub, in their own counterexample.** Using
  Theorem A (finite min-norm candidates) on the two fan pin-disks
  `S = B̄(p₁,r)∩B̄(p₂,r)` (pins of the pairs `(c0,c±)`):

| configuration | `max_j\|H−p_j\|−r` (fixed hub) | `h* = argmin_{h∈S}\|h\|` | `\|h*\|` vs `ρ=5/8` | active at `h*` |
|---|---|---|---|---|
| exact `ε=0` | `−5.83·10⁻²` (both slack) | `(0.405573, 0)` | `0.4056 < 0.625` ✓ | **both** `\|h*−p_j\|−r = 0` |
| `ε=10⁻²` | `−8.11·10⁻²` | `(0.369930, 0)` | `0.3699 < 0.625` ✓ | **both** active |
| `ε=10⁻³` | `−6.07·10⁻²` | `(0.401786, 0)` | `0.4018 < 0.625` ✓ | **both** active |

In these three configurations the hub min-norm point happens to lie on **both** pin circles, so it
saturates both fans (hub strict, all fan radii `≤ r` with equality on the active pairs, by C879).
Two over-strong readings are corrected here (lead, team-message ea3a0b34):

* **`min_{h∈S}|h| ≥ ρ` is not a "norm-pinned hub" continuation branch.** By Theorem A/B it means
  there is **no strict-feasible hub at all** (a ≤3-constraint witness of
  `STRICT-HUB-FINITE-DISJUNCTION.md` §3 fires): the chain — hence that configuration class — is
  *excluded*. Do not read it as "move the endpoints and continue".
* **The min-norm point need not be active.** `h* = argmin_{h∈S}|h|` lies on a disk boundary unless
  `h* = 0 ∈ int S` (all fan constraints slack at the origin), in which case the min-norm move
  saturates nothing. So "min-norm is always active" is false. The correct finite statement: a hub
  position saturating a fan exists iff `∂S ∩ B(0,ρ) ≠ ∅` is reachable, and `h*` realises it exactly
  when `h* ∈ ∂S`. Whether the strict ring domain can present `0 ∈ int S` (i.e. whether `0` is
  admitted as a hub there) is **not settled** and needs its own argument.

Proved dichotomy (Theorem A + Theorem B): `min_{h∈S}|h| < ρ` ⟺ a strict hub exists; at the boundary
`min = ρ` and at `S = ∅` the CQ-failure reading of `STRICT-HUB-FINITE-DISJUNCTION.md` §4 applies.
For the hub **pair** one must keep the central constraints central: the finite active-normal forms
(no hub min-norm move) are in `CENTRAL-COUPLING-NORMAL-FORMS.md`.

Repro:
```
py -3 -B -X utf8 research-2026/team-current/r20-geometry/radial_inward_local.py
py -3 -B -X utf8 research-2026/team-current/r20-geometry/radial_tightening.py
py -3 -B -X utf8 research-2026/team-current/r20-geometry/radial_span_check.py
py -3 -B -X utf8 research-2026/team-current/r20-geometry/lead_counterexample_check.py
```
