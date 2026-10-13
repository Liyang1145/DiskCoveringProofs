# Audit: adjacent-ring fan hub-feasibility disk-intersection mechanism

Reviewer: r20-geometry. Inputs read only; `lead/` untouched; no claim registered.
Evidence: `audit_fan_disk_mechanism.py/.out.txt/.json`, `audit_tie_uniqueness.py`,
`audit_tie_uniqueness_fine.py/.out.txt/.json`.

**Verdict: the mechanism is correct under the stated hypotheses, and each hypothesis has now an
identified role.** No counterexample found. Two scope caveats and one quantitative caveat below.

## 1. Which half of the conclusion is automatic, which is not

Setup as in the lead's note: ring radius $r$, centres $c_i,c_j$, $d=|c_j-c_i|$,
$m=\frac{c_i+c_j}{2}$, $n$ the unit radical direction, $k=\sqrt{r^2-d^2/4}$, $U$ the common tie
point on $\partial D$ covered by both rings, orientation fixed by $U=m+t_+n$, $V=m+t_-n$ the
other crossing of $\partial D$ by the radical line.

* $m\in\operatorname{int}D$ is automatic: $|m|\le\frac{|c_i|+|c_j|}2\le s=\sqrt{1-r^2}<1$.
  Hence $t_-t_+=|m|^2-1<0$, i.e. $t_-<0<t_+$ with no extra hypothesis.
* $U$ covered by both rings gives $|U-c_i|\le r$. Since
  $|m+tn-c_i|^2=\frac{d^2}4+t^2$, this is exactly $|t_U|\le k$, i.e.
  $$t_+=|t_U|\le k .$$
  Therefore $p_{out}=m+kn\notin\operatorname{int}D$ **automatically** — this half of the lead's
  conclusion does not use the tie-uniqueness at all.
* The other half, $t_-<-k$ (equivalently $p_{in}=m-kn\in\operatorname{int}D$, equivalently $V$ is
  covered by at most one of the two disks), is exactly the statement that $V$ is not a second tie
  inside the common overlap. Proof from the hypotheses: $V$ is equidistant, so "covered by one of
  the two" $=$ "covered by both" $=$ "$V$ lies in the common overlap"; $V$ is equidistant and
  $\ne U$, contradicting the "unique equidistant point in the common overlap" hypothesis.
  So (ii) $\iff$ tie-uniqueness.
* Hub half: the two radius-$r$ circles through $c_i,c_j$ are centred at $p_{in},p_{out}$, hence
  *(fixed in Round 3 — my earlier "cap" description was wrong)*
  $\{\text{circumradius}(c_i,c_j,h)\le r\}$ is the **symmetric difference of the two disks** (the
  two *crescents*), via the identity
  $4y^2(R_c^2-r^2)=\big(|h-p_{in}|^2-r^2\big)\big(|h-p_{out}|^2-r^2\big)$ with
  $F_{in}-F_{out}=4ky$; points inside *both* disks (including $y<0$, e.g. $h=m$ where $R_c=\infty$)
  have $R_c>r$, and the base line $y=0$ is excluded (circumradius $+\infty$). For a strict hub
  $|h|<1-r$ and $p_{out}\notin\operatorname{int}D$: $|h-p_{out}|\ge|p_{out}|-|h|>1-(1-r)=r$, so
  $F_{out}>0$ and, since $|h-p_{in}|\le r$ forces $y<0$ automatically (see
  `AUDIT-CLOSED-H-AND-STRICT-HUB.md` §0–§2),
  $$\text{circumradius}(c_i,c_j,h)\le r\iff h\in B(p_{in},r)$$
  — the "inward side" clause is automatic, no separate side check needed. This uses only the
  **automatic** half. The per-hub feasible region is therefore $\bigcap B(p^{ij}_{in},r)\cap
  B(0,1-r)$ over the fan's adjacent pairs: 4 disks for one fan, 5 for the other — convex.

## 2. Verification on the certified cover (all equalities saturated)

Exact-rational centre data, mpmath 40 digits, ties recomputed by angular bisection (independent of
the radical-line formula). For all nine adjacent ring pairs ($r=r^\*=0.3799838531198387$):

| pair | d | k | $t_+-k$ | $t_-+k$ | $\lvert p_{in}\rvert$ | $\lvert p_{out}\rvert$ |
|---|---|---|---|---|---|---|
| 7-1 | 0.65947 | 0.18885 | $-4\cdot10^{-17}$ | $-1.62$ | 0.6229 | 1.0000000 |
| 1-8 | 0.65947 | 0.18885 | $-5\cdot10^{-17}$ | $-1.62$ | 0.6229 | 1.0000000 |
| 8-6 | 0.52971 | 0.27247 | $-3\cdot10^{-17}$ | $-1.40$ | 0.4868 | 1.0000000 |
| 6-4 | 0.45110 | 0.30580 | $-7\cdot10^{-17}$ | $-1.38$ | 0.3960 | 1.0000000 |
| 4-9 | 0.55500 | 0.25958 | $-5\cdot10^{-17}$ | $-1.47$ | 0.4847 | 1.0000000 |
| 9-10 | 0.59674 | 0.23529 | $-8\cdot10^{-17}$ | $-1.53$ | 0.5294 | 1.0000000 |
| 10-3 | 0.55500 | 0.25958 | $-8\cdot10^{-17}$ | $-1.47$ | 0.4847 | 1.0000000 |
| 3-5 | 0.45110 | 0.30580 | $-5\cdot10^{-17}$ | $-1.38$ | 0.3960 | 1.0000000 |
| 5-7 | 0.52971 | 0.27247 | $-5\cdot10^{-17}$ | $-1.40$ | 0.4868 | 1.0000000 |

So on the extremal object: $t_+=k$ (tight arcs), $p_{out}\in\partial D$ exactly (the allowed
boundary case), $p_{in}$ strictly inside with margin $\ge0.38$. Hub half: the hub lies exactly on
$|h-p_{in}|=r$ for 7 of the 9 faces (faces 1,2,3,4,6,8,9 saturated, $|h-p_{in}|-r\sim10^{-16}$)
and strictly inside by $2.84\cdot10^{-3}$ for the two unsaturated faces 5,7; in every case
$|h-p_{out}|-r\ge0.37>0$. Consistent with the registered "18 of 20 radii active" picture; note
2 faces are **not** saturated, so any argument that assumes all fan disks are active at the
extremal configuration is false as stated.

Constructed families (independent check of the two regimes):
* partial overlap, 8 disks $r=1/2$, $|c|=0.7$: $t_+-k=-6.9\cdot10^{-2}$ (U covered with slack),
  $t_-+k=-1.2$, $|p_{in}|=0.2245$, $|p_{out}|=1.0689$.
* exact arc tangency (zero overlap), $|c|=0.60209$: $t_+-k\approx0$ ($U$ exactly on both circles),
  $t_-+k=-1.1$, $|p_{in}|=0.1125$, $|p_{out}|=1.0000000$.

## 3. The four degeneracies

1. **$d=2r$ (tangent ring circles).** Impossible under the hypotheses: then $k=0$, so
   $t_+\le k=0$ contradicts $t_+>0$. Equivalently $B(c_i,r)\cap B(c_j,r)=\{m\}$ with
   $m\in\operatorname{int}D$ cannot contain $U\in\partial D$. So this degeneracy cannot be reached;
   no separate treatment is needed provided $|c_i|,|c_j|\le s$ is used.
2. **Collinear hub $h$ (with $c_i,c_j$) — this item was WRONG and is CORRECTED.**
   In the local frame $|h-p_{in}|^2-|h-p_{out}|^2=4ky$, so a strict hub in the $p_{in}$ disk
   satisfies $r<|h-p_{out}|$ together with $|h-p_{in}|\le r$, hence $4ky<0$, i.e. $y<0$
   **strictly**: the correct inward side and non-collinearity are automatic, no extra hypothesis.
   My earlier numeric "collinear probe" moved $h$ along the base line *without* imposing
   $|h-p_{out}|>r$; on that line the two distances are equal, so such points are never strict hubs.
   Corrected statement and the cap description of $\{\text{circumradius}\le r\}$:
   `AUDIT-CLOSED-H-AND-STRICT-HUB.md` §0–§1.
3. **Closed hub domain $|h|=1-r$ — CORRECTED in Round 3.** For pairs with $|p_{out}|=1$ (the
   extremal cover has this on all nine pairs) the single radial point $h^\*=(1-r)p_{out}$ satisfies
   $|h^\*-p_{out}|-r=5\cdot10^{-17}$ and, on the certified chain, $|h^\*-p_{in}|-r=-0.363<0$. By
   the product identity the face condition holds at $h^\*$ identically ($R_c=r$), and
   $|h^\*-p_{in}|\lessgtr r\iff y_{h^\*}\lessgtr0$: so **all nine certified $h^\*$ are legitimate
   inward points, not bad points** (the lead's correction; my earlier "spurious extra point" label
   was wrong and is withdrawn). The closed-domain discrepancy is one-sided: $h^\*$ is *missed*
   (face condition true, mechanism disk not containing it) exactly when $y_{h^\*}>0$; and the
   mechanism region has **no** extra points off the base line. **Round-4 fix:** on the base line
   $y=0$ the mechanism region meets the closed domain exactly in the degenerate stratum
   $h\in\{a,b\}$ (ring centres), where the circumradius has no value (direction-dependent limit
   $d/(2|sin\theta|)$); so the blanket "no extras anywhere" was wrong and is corrected (see
   `AUDIT-CLOSED-H-AND-STRICT-HUB.md` Fix 3 / `STRICT-HUB-FINITE-DISJUNCTION.md` §0). The stratum
   lies on $|h|=1-r$ and never in the strict domain. Patch: add those missed points (≤1 per edge);
   for an *iff* reading name the two degenerate points as well.
   For strict hubs $|h|<1-r$ no such point exists (the lead's hypothesis).
4. **Tie uniqueness in the common overlap.** This is the only hypothesis I could not derive.
   Corrected adversarial search (both centres at distance $rU\le r$ from $U$, $|c_k|\le s$, $d<2r$;
   60 Nelder–Mead starts + $61\times61\times11$ grid): minimum of
   $F=\max(|V-c_i|,|V-c_j|)-r$ is $+8.5\cdot10^{-6}$; the infimum is approached only in the
   degenerate coincidence limit $d\to0$ (worst point $d=10^{-6}$, where also
   $|p_{in}|\to1^-$). Over the same admissible set $\min(m\cdot n)=-0.86$ (so the naive
   "$m\cdot n\ge0$" sufficient condition is false) but $\sqrt{\text{disc}}-k\ge3.1\cdot10^{-2}$
   compensates. Conclusion: on everything tested the hypothesis is *redundant* (so the mechanism is
   applicable even where the notes do not check it), but I have **no proof**, and two caveats:
   (a) "adjacency of essential arcs" alone does not imply uniqueness — a third ring strictly closer
   at $V$ produces two ties for the same pair, so the "no triple" clause is load-bearing;
   (b) there is **no uniform margin**: $|p_{in}|=1-\Theta(d)$, so any interval certificate built on
   "$p_{in}\in\operatorname{int}D$" must either exclude small $d$ or carry the $d$-dependence.

## 4. Scope statement

Confirmed: for every adjacent ring pair produced by the ring/fan structure with the four
hypotheses, the mechanism's two-sided conclusion holds; per hub the feasible set is
$\bigcap_{\text{pairs}}B(p_{in},r)\cap B(0,1-r)$, convex, and the hub constraints used in the
fan reduction are exactly these disk containments. Not claimed: any global radius inequality, a
proof of hypothesis 4, or that the extremal hub is a vertex of that convex set (2 of the 9 face
disks have slack $2.8\cdot10^{-3}$, so it is not).

Repro:
```
py -3 -B research-2026/team-current/r20-geometry/audit_fan_disk_mechanism.py
py -3 -B research-2026/team-current/r20-geometry/audit_tie_uniqueness.py
py -3 -B research-2026/team-current/r20-geometry/audit_tie_uniqueness_fine.py
```
