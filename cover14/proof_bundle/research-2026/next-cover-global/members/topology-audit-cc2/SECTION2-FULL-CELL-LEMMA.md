# §2 / §3 of OWNER-COUNT-UNIFICATION.md — independent audit (final, corrected)

Route commandcode2/deepseek/deepseek-v4-flash. Write scope: this directory.
This version SUPERSEDES all earlier drafts of this note in this directory and withdraws two
false corollaries I had derived (see §0).

## 0. Withdrawals

1. **"No singleton owner" WITHDRAWN (FALSE).** I had defined ownership with STRICT inequalities
   and declared tie points unowned, then concluded that no site can own a singleton arc. That
   is wrong: with non-strict nearest ownership a singleton owned point CAN exist, exactly at
   the tangency/tie configuration (the site's own disk tangent to S^1 at x while x is at
   distance exactly r from another site). This is precisely why the ε outward clip in §3 is
   necessary, as the lead said. The clip, not a lemma about ownership, is what removes the
   case.
2. **"3-ring dual face is excluded" WITHDRAWN (FALSE).** {i−1, i, i+1} is a legitimate pairwise
   adjacent triple in the 11-cycle, so an empty (3-ring) pocket can occur; the q11 generator
   already includes empty ears. My "three pairwise-adjacent vertices cannot exist in a cycle"
   reasoning was wrong (it confused a triangle subgraph with pairwise adjacency).
3. Earlier withdrawals stand: my F3 hub-facet-midpoint counterexample (illegal: hubs on S^1),
   the tangent-configuration ownership jump (not a cover; covering radius ≈0.735 >> U).
4. The claim that the CURRENT generator's full_canon is not a group invariant is also
   WITHDRAWN: lead/gen_k10_fixed_copy.py uses the correct reflection v ↦ sh − v, and a faithful
   replica passes my invariance test with 0 violations over 3240 group-transformed paths and
   produces the same 68 classes as my independent canonicalisation. The non-invariance I
   measured belongs to the OLD members/topology/gen_k10_catalogue.py (v ↦ 2sh − v).

## 1. What survives (the independently proved part) — full-cell lemma

Setting: D = closed unit disk, S^1 = ∂D; finitely many distinct sites c_i ∈ int D; W_i is the
closed convex full-plane Voronoi cell of c_i, so c_i ∈ int W_i.

**Lemma (full-cell).**
(1) If x ∈ W_i ∩ S^1 lies in int W_i, then W_i ∩ S^1 contains a positive-length arc around x:
    an open ball B(x,δ) ⊂ W_i meets S^1 in such an arc.
(2) If W_i ∩ S^1 is a singleton {x} with x ∈ ∂W_i, then the tangential configuration is forced:
    a supporting line ℓ of W_i at x has distance 1 from the origin and W_i lies OUTSIDE ℓ, the
    site's disk is tangent to S^1 at x, and (in a cover) x is a tie point equidistant to another
    site within r. So the singleton case is possible only as an ownership TIE, and it is
    removed only by the outward clip of §3 — not by any strictness lemma.
(3) If W_i ∩ S^1 = ∅, then W_i ⊂ int D and W_i is compact: indeed if y ∈ W_i had |y| > 1, the
    open cone spanned by a ball B(c_i,ε) ⊂ int W_i and y would be contained in W_i by convexity
    and would meet S^1 in a positive-length arc, contradicting W_i ∩ S^1 = ∅; and a closed
    bounded set with dist(W_i, S^1) > 0 sits in the open disk. Hence W_i ∩ ∂D_(1+ε) = ∅ for all
    small ε > 0, and such a site acquires no boundary ownership from the clip.
Item (3) is what §3 line 17 needs for the cells with no S^1 intersection; item (2) is why the
clip is needed for the tangency case; item (1) is what allows an owner arc to be treated as an
arc of positive length whenever the owned point is interior to the cell.

## 2. Verified numeric constants for §4 (recomputed independently, mpmath 40 digits)

asin(2ρ)+7asin(ρ) with ρ=r_ε/R_ε: π−value = +4.92e−2 at ρ=U, +3.30e−2 at ρ=1/3−1e−9;
norm guard √(1−ρ²)−s/R_ε = +7.07e−4 at ε=1e-3 and +7.08e−6 at ε=1e-5. So the hypotheses
r_ε/R_ε<1/3 and the owner-arc length bound have room for small ε. Script: geo_check.py.

## 3. What this audit does NOT establish

No metric exclusion, no q11 pocket enumeration, no k11 catalogue. The two reliable endpoints of
this audit are (i) the full-cell lemma above, and (ii) the independent enumeration/set-equality
result in FINDINGS.md F0 (1000 = 68+932, exact class-set equality with both the stored overcounted
list and the lead's corrected list, with the odd-N n12 calibration 51↔51).
