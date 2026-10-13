# SOURCE-INWARD-ROOT-AUDIT — the premise bridge C450/C451/C464 → 9+2 inward-root

Assigned source audit of the bridge that every `r ≤ 0.38` cover in the reduced class is
an **inward-root 9-ring + 2-hub** configuration. Read from the actual proofs
(`../solo-20260922/INNER-ROOT-DOMINANCE.md`, `../solo-20260922/N11-LOW-RADIUS-REDUCTION.md`,
`../solo-20260922/M10-038-EXCLUSION.md`), with `claim_get` on C450, C451, C464, and the
consumers `lead/VORONOI-BOUNDARY-REDUCTION.md` (VBR) and `flash-structure/LOCALITY-LEMMA-RING.md` (C799).
No claim registered; no subagent.

**Verdict, stated narrowly (not a global "complete").** On the three questions the task
named: (a) the inner-root replacement preserves coverage of the whole disk, not merely
the boundary — C464's two-region proof gives `D ∩ B(outer) ⊂ D ∩ B(inner)` outright, and
the substitution is per disk; (b) the non-deletability of both hubs is a valid deduction
from the `m = 10` theorem, whose proof is uniform in `r ≤ 19/50`; (c) after the
replacement the nearest-owned switch domain must be **rebuilt, not carried over** — the
*actual covered* arcs are invariant but the *owned* arcs and switches are not (§3.1);
what survives is the arc count, the half-width bound `≤ asin r`, the tiling
`ΣΔ_i = 2π`, coverage of `D`, and `covering radius ≤ r`. Distinctness of the eleven
sites on the replaced configuration is *proved* in §3.3, not assumed. Three items are
registered **non-claims** of the sources (not gaps of the bridge), listed in §5. I do
not assert more than this.

---

## 1. C464: does the inner-root replacement preserve whole-disk coverage?

**The theorem (verbatim structure).** Let `D` be the unit closed disk, `0 < r < 1`,
two same-radius centres `ρ_-u`, `ρ_+u` on a ray with `0 < ρ_- ≤ ρ_+` and
`ρ_-ρ_+ = 1 − r²`, covering the same actual arc of `∂D` (tangency/double root allowed).
Then `D ∩ B(ρ_+u, r) ⊂ D ∩ B(ρ_-u, r)`.

**Where the product relation comes from (I verified this in the sources).** Two radius-`r`
disks on one ray cover the same boundary arc iff they pass through the same two trough
points of the unit circle, at angles `±θ`. The condition `|ρu − e^{iθ}| = r` gives
`ρ² − 2ρ cos θ + (1 − r²) = 0`, a quadratic in `ρ` whose two roots satisfy
`ρ_-ρ_+ = 1 − r²`; conversely `ρ_± = cos θ ± sqrt(r² − sin²θ)`. So the hypothesis is
exactly "same arc", and the *inner* root is the smaller of the two.

**The proof, with the two regions checked.** With `c := (ρ_- + ρ_+)/2` and `x := p·u`:

* `x ≤ c`: `|p − ρ_+u|² − |p − ρ_-u|² = (ρ_+ − ρ_-)(2c − 2x) ≥ 0`, so `p ∈ B(ρ_+u,r)`
  implies `p ∈ B(ρ_-u,r)`.
* `x ≥ c`: using `|p| ≤ 1` and `1 − r² = ρ_-ρ_+`,
  `|p − ρ_-u|² ≤ 1 − 2ρ_-x + ρ_-² ≤ 1 − 2ρ_-c + ρ_-² = 1 − ρ_-ρ_+ = r²`. The middle
  step needs `x ≥ c ≥ 0` **and** the final identity needs `ρ_-ρ_+ = 1 − r²`. Both hold.

**The one implicit step, verified.** The step `−2ρ_-x ≤ −2ρ_-c` requires `ρ_- ≥ 0`,
and the identity `1 − 2ρ_-c + ρ_-² = r²` is exactly `2ρ_-c − ρ_-² = 1 − r²`, i.e.
`2ρ_-·(ρ_-+ρ_+)/2 − ρ_-² = ρ_-ρ_+ = 1 − r²`. No further hypothesis. **The second region
does not assume the outer disk covers `p`** (the file emphasises this: the entire cap is
covered by the inner disk outright). So the containment is unconditional, and by
symmetry of the argument under `p → −p` it covers the whole disk.

**Replacement preserves coverage.** C464's own "意义" paragraph states the reduction:
"对任何覆盖构型，可独立将每个边界盘的外根换成内根，保留其他盘与`r`，得到覆盖`D`的内根代表"
— for any covering configuration, each boundary disk's outer root may be replaced
**independently** by its inner root, keeping the other disks and `r`, yielding a covering
representative. Since the containment is `D ∩ B(outer) ⊂ D ∩ B(inner)`, replacing disk
`j` inside a cover `∪_i (D ∩ B_i) = D` keeps the union equal to `D`. **No loss of
interior coverage anywhere in `D`** — this is the point the task asked about, and the
source proof delivers it (it is not merely a boundary statement).

*Registered scope note (verbatim):* the file calls this an **存在性归约** (existence
reduction) and explicitly does not claim uniqueness of the representative, nor that the
replaced configuration lies in some extra geometric family; and it warns that if one
studies *all* root-labelled configurations the outer root must not be erased.

**Diagnostic (not evidence):** with `ρ_+ = 1`, `ρ_- = 1 − r²`, the two roots satisfy
`ρ_-ρ_+ = 1 − r²` for every tested `r`; `2ρ_- ≥ 1 − r² ⟺ ρ_+ ≤ 2`, which holds because
`ρ_+ ≤ 1 + r < 2` for the whole allowed range; and `c ≤ 1 ⟺ ρ_+ ∈ [1−r, 1+r]`, its
defining interval. Scripts in `scratch-scaletest/check_c464_geom.py`.

---

## 2. C450/C451: is "9 boundary + 2 hubs, both non-deletable" correctly deduced?

**(a) `m ≥ 9`.** Each boundary disk meets `∂D` in an arc of *half-width* `≤ asin r`
(a radius-`r` disk's intersection with the unit circle has angular half-width at most
`asin r`; VBR uses the same bound). These `m` arcs cover `∂D`, so `m·asin(r) ≥ π`.
With `r ≤ 19/50` and `8 asin(19/50) = 3.11837… < π` (equivalently `19/50 < sin(π/8)`,
square-comparable as `sqrt2 < 889/625`, i.e. `790321 > 781250`), we get `m ≥ 9`.
*Verified numerically:* `asin(19/50) = 0.389796…`, `8·asin(19/50) = 3.11837 < π`;
`(19/50)² = 0.1444 < (2−√2)/4 = 0.1464466`; `889² = 790321 > 781250 = 2·625²`.

**(b) `m ≤ 10`.** A boundary disk has centre norm `≥ 1 − r > r` (it meets `∂D`), so
every point of it has norm `≥ 1 − 2r > 0`: **no boundary disk covers the origin**.
Since the eleven disks cover `D`, some disk covers the origin, hence `m ≤ 10`.

**(c) `m = 10` is excluded by C450.** The source's own argument: if `m = 10`, the
boundary is covered by those ten disks and the eleventh is a single hub — precisely the
configuration `M10-038-EXCLUSION.md` excludes. That file's theorem is
**`r > 19/50` whenever ten disks touch and cover `∂D` and the eleventh covers `D`**,
and its proof *fixes `R = 19/50` and enlarges all eleven radii to `R`* ("把全部半径扩大到`R`。
原十个边界盘仍接触且覆盖`∂D`；十一盘仍覆盖`D`"), so it applies to every `r ≤ 19/50`,
not merely `r = 19/50`. Its scope line is explicit that it covers redundant boundary
arcs, overlaps, tangential boundary disks and outer roots, and that it does *not* cover
9 + 2. Certified by two independent arithmetic kernels over 36 closed `e`-segments.
**So `m = 9` follows, and the deduction is a two-step (counting + imported theorem)
argument — the pair `m ≥ 9, m ≤ 10` alone gives only `m ∈ {9,10}`.**

**(d) Both non-boundary disks are strictly interior.** A non-boundary disk that meets
`D` must lie strictly inside: if it had an interior point and an exterior point of `D` it
would cross `∂D` (convexity/connectedness), and the case "disk contains `∂D` while not
meeting it" is impossible for `r < 1`. The radial criterion is `|h| + r < 1`, as the
source states. If an interior disk met `D` in the empty set it would contribute nothing.

**(e) Both hubs are non-deletable — the deduction is valid.** The source argues: if a
non-boundary disk neither meets `D` nor is needed (delete it, the remaining ten still
cover `D`), then add *any* radius-`r` disk tangent to `∂D`; the result is "ten boundary
disks + one hub covering `D`", contradicting C450. I checked the two sub-cases:
* the deletable-but-intersecting case: deleting it leaves ten disks covering `D`, of
  which nine touch `∂D`; adding a tangent disk makes **ten** boundary disks plus one
  hub (the tangent disk touches `∂D` at exactly one point, and the nine original arcs
  still cover `∂D` since coverage is unchanged), which is the excluded configuration;
* the disjoint case: same conclusion with a hub that is not needed at all.
The tangent-disk existence is trivial (tangent at any point of `∂D`). **Non-deletability
therefore holds for the inward-root representative too**, since it holds for every
covering configuration by the same argument.
*Registered non-claim of the source (must not be overstated):* it does **not** claim
that all nine boundary disks are individually necessary, nor that arcs are
non-overlapping, nor uniqueness of the 9+2 configuration. The bridge does not need any
of those.

---

## 3. Does the replacement keep the cellulation nondegenerate?

This is the part the task flagged as "generic cellulation degeneracy". The relevant
consumers are VBR §1–§3 (ownership, eleven nonempty faces, switch degree 3) and
C799 (locality). I checked each requirement against the replaced configuration.

**(3.1) CORRECTED — the *actual* covered arcs are invariant, the *owned* arcs and
switches are NOT.** My earlier version of this item conflated the two notions. The
distinction matters:

* **Actual covered arc** `I_i^{cov} := ∂D ∩ B(c_i, r)`: the set of boundary points
  covered by disk `i`. C464's hypothesis is that the outer and inner disks cover the
  same actual arc, and the replacement keeps it *literally unchanged* — C464's own
  statement says the two disks "在∂D上覆盖同一实际弧" and the conclusion preserves that arc.
  So `I_i^{cov}` is invariant.
* **Owned (nearest-centre) arc** `I_i^{own} ⊆ I_i^{cov}`: the set of boundary points
  where disk `i` is the *nearest* centre. This is **not** invariant: the replacement
  moves the ring centre radially inward, hence changes the radical line
  `(c_i − c_j)·x = (|c_i|² − |c_j|²)/2` between `c_i` and each neighbour, hence changes
  the equal-distance locus. **The old switch point need not remain the new switch
  point**, and the widths `Δ_i` need not be the old ones.

**What is actually required downstream, and it is available by re-derivation (not
invariance):** take the replaced configuration and *rebuild* the switch domain in it.
VBR §1's ownership/uniqueness argument (`arc lengths < π` because `2 asin r < π/2 < π`;
inside an overlap only the two disks can win; the difference of squared distances is an
affine function restricted to the circle with opposite endpoint signs ⟹ an odd number
of transverse zeros, and a tangent zero cannot coexist with a transverse one) applies to
**any** configuration of nine distinct boundary disks with short arcs, hence to the
replaced one. So:

* the nine owned arcs exist, have positive length, and their cyclic order is the
  boundary order of the nine actual arcs;
* the nine switches exist and are unique in their overlaps;
* the anchors `U`, the widths `Δ`, the switch set and the covering radius are
  **re-derived from the replaced configuration**; they may differ from the original
  ones and nothing downstream needs them to agree.

**What *is* invariant and is what C464 must guarantee:** each actual arc `I_i^{cov}`,
hence the fact that the nine boundary disks' arcs cover `∂D` and have half-width
`≤ asin r`; and `∪_i (D ∩ B_i) = D`. The arc-length ledger's *upper* bounds
`Δ_i ≤ 2 asin r` therefore still hold for the new widths, and `ΣΔ_i = 2π` still holds
because the owned arcs tile `∂D` (they are the boundary-ownership partition). The
covering radius of the replaced configuration is `≤ r` (coverage only improved inside
`D`); it need not equal `r`.

**(3.2) No *boundary* disk covers the origin (used twice).** Title corrected: the
statement is about boundary disks only, and it is `m ≤ 10`'s input. For a boundary disk,
`|c| ≥ 1 − r > r` as in §2(b), so every point of such a disk has norm `≥ 1 − 2r > 0`.
After the replacement the nine ring centres satisfy `|c_i| ≤ sqrt(1 − r²)` (C464's
conclusion), and C451's count `m = 9` holds for the replaced configuration too (it is
again a cover by eleven equal disks at the same radius); the two hubs remain strictly
interior, `|h| + r < 1`.

**(3.3) Site distinctness is a consequence, not an assertion — and it must be proved.**
My earlier text asserted it. Here is the proof, and it uses C451 *on the replaced
configuration*, not merely on the original.

* *Distinctness of the nine ring centres.* Each ring disk meets `∂D` in an arc of
  positive length (C464 preserves the actual arcs) and these nine arcs are pairwise
  distinct sets (they are the nine actual covered arcs in their cyclic order, and a
  boundary disk that is nobody's unique coverer would be deletable, excluded by C451).
  So ring `i` has at least one boundary point that ring `j` (`j ≠ i`) does not cover.
  At such a point `p`, `|p − c_i| ≤ r < |p − c_j|`, hence `c_i ≠ c_j`.
* *Distinctness of the two hubs from everything.* A hub does not touch `∂D` (this is
  `m = 9`, applied to the replaced configuration). A ring centre is a boundary disk's
  centre. So a hub equals a ring centre only if that disk both touches and does not
  touch `∂D` — impossible. The two hubs differ from each other because if `h_1 = h_2`
  the pair would be one disk counted twice, giving only ten distinct disks.
* *Nonempty interiors.* With distinctness in hand, each site is its own nearest centre
  inside a small ball around it (all distances to the other centres are positive), and
  each such ball meets `int D`: ring centres lie in `D` (C464's `|c_i| ≤ sqrt(1−r²) < 1`),
  hubs in `int D`. So every one of the eleven nearest-centre cells has nonempty
  interior. VBR §3's premise is thereby *established* for the replaced configuration,
  rather than taken over from the original.

**(3.4) Switch degree 3 and transversality.** At a switch the two ring sites are
equidistant at distance `≤ r` and all other sites are strictly farther (they do not
cover the switch); the bisector is a secant because its distance from the origin is
`||c_i|² − |c_j|²| / (2|c_i − c_j|) ≤ (|c_i| + |c_j|)/2 ≤ sqrt(1 − r²) < 1` — the
`sqrt(1 − r²)` bound uses exactly C464's conclusion, so the argument holds *after*
replacement (VBR §3 records precisely this).

**(3.5) Degeneracies are tolerated, not assumed away.**
* *Cocircular Voronoi vertices* of degree `> 3`: VBR §3 states "high-order cocircular
  coincidences **decrease** the counts, not increase them; degenerate zero-length edges
  are not counted", so the counts `v ≤ 11`, `e ≤ 21` remain available and equality
  requires trivalence. Consumers handle the non-trivalent case by refinement
  (`flash-structure/GLOBAL-TOPOLOGICAL-REDUCTION.md`: a refinement may create ring-only
  faces, but every ring-only face of the refinement is still a consecutive triple since
  the clique number of `C_9²` is 3, and `q, K`, degrees are explicitly
  refinement-dependent).
* *Tangency* of boundary arcs: C451 explicitly counts tangential boundary disks, and
  `ARC-COORD`'s domain keeps `t_i = arcsin r` (the double root `ρ = sqrt(1−r²)`) as an
  admitted boundary; C464's proof includes equalities in both regions.
* *Duplicate centres*: excluded by §3.3's proof (ring centres separated by private arc
  points; hubs strictly interior so they cannot coincide with a ring centre; the two
  hubs distinct because otherwise only ten distinct disks).

**(3.6) What the replacement does *not* preserve (registered, not a gap).** The file's
own caveat list: it does not preserve a chosen arc *sub*-partition, does not keep the
original ring centres fixed, does not put the replaced configuration into any extra
geometric family, and does not randomise the disk radius. Downstream consumers that
need "the inward-root representative" are therefore correct to take the *replaced*
configuration, and those that need the *original* root labels (e.g. any equal-root
classification) must keep them. Both statements are in the source.

---

## 4. Chain summary with exact premises

| step | statement | premise | source |
|---|---|---|---|
| 1 | each radius-`r` disk covers a boundary arc of half-width `≤ asin r` | `r < 1` | VBR §1; `N11-LOW-RADIUS-REDUCTION.md` §"边界盘个数" |
| 2 | `m ≥ 9` | `8 asin(19/50) < π` ⇔ `19/50 < sin(π/8)` | same, with the integer certificate `790321 > 781250` |
| 3 | `m ≤ 10` | no boundary disk covers the origin (`\|c\| ≥ 1−r > r`), origin must be covered | same |
| 4 | `m ≠ 10` | **C450** `M10-038-EXCLUSION.md` (10 boundary + 1 hub ⇒ `r > 19/50`), applied after enlarging all radii to `R = 19/50` | that file §1–§4, two kernels, `DUAL-MANIFEST.json` |
| 5 | the two non-boundary disks are strictly interior | convexity/connectedness argument; radial form `\|h\| + r < 1` | `N11-LOW-RADIUS-REDUCTION.md` §"两个非边界盘…" |
| 6 | both hubs non-deletable | delete + add tangent disk ⇒ excluded 10 + 1 configuration | same |
| 7 | inner-root replacement preserves `D`-coverage | `ρ_-ρ_+ = 1 − r²` (same-arc condition), two-region algebra | **C464** `INNER-ROOT-DOMINANCE.md`, full proof read |
| 8 | after replacement `\|c_i\| ≤ sqrt(1 − r²)` | C464 conclusion | same |
| 9 | **actual covered arcs** invariant; **owned arcs / switches / widths NOT invariant** — the switch domain is *rebuilt* on the replaced configuration, and C464 guarantees only that the substituted centre lies on the same ray and gives an inner disk whose actual arc is unchanged | step 7 + C905-style recomputation (VBR §1 argument applies to any configuration with short arcs) | VBR §1; §3.1 above |
| 10 | arc count 9, half-width bound `≤ asin r`, tiling `ΣΔ_i = 2π`, `covering radius ≤ r` | steps 7–9 | VBR §1 (definition of actual arc), `ARC-COORD` (upper bound) |
| 11 | site distinctness on the replaced configuration; eleven nonempty cells; switch degree 3; counts `v ≤ 11, e ≤ 21` | distinctness proof in §3.3 (uses C451 on the replaced configuration) + `\|c_i\| ≤ sqrt(1−r²)` | VBR §3, §3.3 above |
| 12 | nondegeneracy under refinement; ring-only faces are consecutive triples | clique number of `C_9²` is 3 | `GLOBAL-TOPOLOGICAL-REDUCTION.md` degeneracy section |

---

## 5. Registered non-claims (explicitly not gaps of this bridge)

1. **Uniqueness / essentiality of the nine boundary disks.** The reduction file states
   "不声称所有九个边界盘各自必要，也不声称弧无重叠或9+2唯一" (it does not claim each of
   the nine boundary disks is necessary, nor non-overlap, nor uniqueness of the 9+2
   configuration). The bridge needs none of these.
2. **All-root-label configurations.** C464's scope paragraph says the replacement may
   not be applied when one studies configurations carrying their outer root ("若研究
   全部标签构型/等号分类，外根仍可能存在，不能抹掉"). The bridge uses only the existence
   of an inward-root representative.
3. **Independent review status.** C464's own last line says "本命题及极性归约待独立研究者
   复核，无新颖性声明"; C451's caliber records "依赖C450"; C450's file header says
   "作者自审，独立研究者复核pending". These are process statuses, not mathematical gaps,
   but a fully unconditional bridge inherits them.

**Items I initially suspected and then confirmed are *present* in the sources:** the
`m = 10` exclusion is a separate theorem with an `r ≤ R`-uniform proof (not a missing
step); the non-deletability argument is a valid deduction; the replacement preserves
interior coverage; and the degenerate-cellulation cases are handled by the sources'
own refinement/clique-count remarks (`q, K`, degrees are refinement-dependent and not
claimed invariant).

No claim registered; no subagent; no lead file modified. Only this file was written.
