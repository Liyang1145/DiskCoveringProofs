# Global-interface audit: conditional closure of r_D(12) = r*

Scope: this single file. Object: D the closed unit disk, twelve equal closed
disks of radius r, centers arbitrary in R², repeats allowed,
r_D(12) = inf max_{p∈D} min_i |p−c_i|. Question audited: **if the remaining k10
root box is completely and validly excluded, does r_D(12) = r* follow
unconditionally?** Inputs taken as established (per instruction, not re-proved
here): C985 (exact attainment, r_D(12) ≤ r*), C986 (all-k9 sharp bound,
r ≥ r* for every 12-disk cover with exactly nine boundary-active disks,
centers arbitrary, projection and same-arc inner-root already inside its
caliber), C998 (no radius-U cover with eleven active disks; and by
enlargement-monotonicity no cover with r ≤ U whose original active count is
eleven), C999 (no radius-U k10 cover with hub distance d ≤ 1/10), plus
C925/C926/FOUNDATIONS (projection, k∈{9,10,11}, hubs), INNER-ROOT-REDUCTION,
the atomic dual certificates with their partition/replay interface, and
`members/structure/hub-line-audit/AUDIT.md` (exact core criterion and box
bounds).

**Verdict: the conditional implication is closed.** No step of the chain
requires an unproved premise other than the stated one (full exclusion of the
root box). Details of the five points requested follow the chain; two of them
turn out to be sharper than the synthesis claims (items 3 and 7 below), and no
counterexample to the chain was found.

## The implication chain

Let r < r* and let C be a 12-disk cover of D at radius r.

1. **Projection.** Replace each center by its projection into D. For p ∈ D,
   |p − π(c)| ≤ |p − c| (π is 1-Lipschitz and fixes D), so the projected
   configuration still covers D at the same radius r. No symmetry or general
   position is used, repeats are preserved (equal centers project equally).
2. **Classification at the original radius.** Classify the *projected*
   configuration at radius r. Every point of S¹ is covered, so the half-widths
   of the active disks satisfy Σ α_i ≥ π with α_i ≤ asin(r) ≤ asin(U), hence
   k ≥ π/asin(U) = 8.50342…, i.e. k ≥ 9; and the disk covering the origin has
   |c| ≤ r ≤ U < 1/2, so |c| + r ≤ 2U < 1: that disk is not active, so
   k ≤ 11. (C926/FOUNDATIONS; tangency counts as active.) The original labels
   are never used — the projected configuration is re-classified from scratch.
3. **k = 9.** C986 applies to that configuration (its caliber explicitly allows
   arbitrary centers reduced by projection, repeats, cocircular and degenerate
   faces) and gives r ≥ r* — contradicting r < r*. No enlargement is used in
   this branch.
4. **k ∈ {10,11}: enlarge to U.** Keep the centers fixed and raise the radius to
   U. For fixed centers, r ↦ (B(c,r) ∩ S¹ ≠ ∅) is monotone, so the active count
   does not decrease; it was already ≥ 10 and C926 bounds it by 11 at U. So the
   enlarged configuration is a radius-U cover with exactly 10 or 11 active
   disks. (No invariance of the active count is claimed or needed.)
5. **Enlarged count 11.** C998 excludes it.
6. **Enlarged count 10.** Apply same-arc inner-root replacement to the ten
   active centers only: the S¹ arcs are unchanged (so the ten activity labels
   are preserved) and, by INNER-ROOT-REDUCTION, each previous D-intersection is
   *contained in* the new one — the inclusion is one-directional, the
   intersections get larger, they are not equal. Hence the result is still a
   radius-U cover with the same ten active disks, now with centers of norm in
   [1−U, √(1−U²)], and the same two inactive centers, each with norm < 1−U. For
   |p| < 1−2U = a0 and any ring |c| ≥ 1−U we have |p−c| ≥ |c|−|p| > U, so no
   ring covers the open core; the closed core is therefore contained in the
   closed union of the two hub disks (closedness of a finite union).
7. **Hub placement.** The core covering plus the box bounds gives, after
   rotation, reflection and hub relabeling, h1 = (x−s, y), h2 = (x+s, y) with
   s = d/2, x, y ≥ 0, and
       s ≤ U,  x ≤ 1−U−1/20,  y ≤ 3U−1,
   whenever 1/10 ≤ d ≤ 2U; and for d ≥ 2U there is **no** legal k10 triple at
   all (see (3) below). So every legal k10 configuration with d > 1/10 either
   lies in the declared root box or is impossible.
8. **Branching on d.** d ≤ 1/10: C999. d ≥ 2U: empty of legal triples by (3).
   Otherwise the chart of step 7 applies and the hub triple lies in the root box
   of `hubline_domain.py`.
9. **The premise (four conjuncts, none of them optional).** The root domain is
   covered by a *finite exact partition* into leaves each of which is validated:
      (i) no pending boxes remain (the stack is empty);
      (ii) the partition is complete and exact — the frontier boxes are exactly
           the canonical widest-dimension bisection closure of the root box,
           pairwise interior-disjoint, with total volume equal to the domain
           volume (this is what `plan_branches.check_frontier` /
           `merge_branches` verify for the sharded runs);
      (iii) every leaf marked infeasible carries a verified necessary-condition
           witness (the three prune predicates), not merely a numeric screen;
      (iv) every leaf marked atomic carries an integer replay of the atomic
           dual certificate (the nonnegative integer weights, rational atom
           locations, and the per-cell capture bound 10·M < T), not an LP value
           or a sampling estimate.
   Emptiness of the queue alone proves nothing: a "partial" state with an empty
   stack is not a complete partition, and a leaf list without validations is not
   an exclusion. Given (i)–(iv), no radius-U k10 cover exists, so every branch
   contradicts r < r*; hence r_D(12) ≥ r*, and with C985 (r_D(12) ≤ r*) this
   gives r_D(12) = r*.

All steps except 9 are proved from the listed inputs. Step 9 is the single
outstanding premise, and it is a conjunction of four verifiable obligations
(empty stack, complete exact partition, validated infeasible leaves, replayed
atomic leaves); nothing else in the chain is conditional.

## Verification of the five requested points

**(1) Projection then classification — sound, and the projection is not a
convenience but a needed hypothesis.** The k-theorems are statements about
configurations (centers + radius), not about the labels of an arbitrary
original system. The chain therefore re-classifies after projecting, which is
also what C986's caliber already assumes ("centers arbitrary R², reduced by
projection and same-arc inner-root"). Two consequences worth recording:
(i) C986 must not be applied to the un-projected configuration if it relies on
centers lying in D — the chain never does; (ii) the projection is 1-Lipschitz
and fixes D, so no radius is lost, and repeated centers stay repeated, which
C986's caliber covers.

**(2) Enlargement: active count monotone — verified, and only the monotone
direction is used.** For fixed c, r₁ < r₂ implies B(c,r₁) ⊂ B(c,r₂), hence
B(c,r₁) ∩ S¹ ≠ ∅ ⟹ B(c,r₂) ∩ S¹ ≠ ∅. The upper bound 11 at radius U is the
origin argument: some disk covers the origin, so its center has norm ≤ U, and
|c| + U ≤ 2U = 0.72220… < 1, so that disk is inactive at radius U and k ≤ 11.
(Tangency is handled by using closed disks throughout: "active" means
B(c,U) ∩ S¹ ≠ ∅, which includes tangency, and the containment above is the
closed containment.) Nothing in the chain asserts that the active count is
preserved, so the caveat in the interface audit is correct and harmless.

**(3) The face s = U — doubly excluded, and the d ≥ 2U branch is stronger than
"excluded by a certificate": it is empty.** Independently derived (and verified
symbolically) from the exact core criterion: in the case x ≥ a0, inactivity
x+s < 1−U together with x ≥ a0 gives s < 1−U−a0 = U; in the case x < a0, the
bisector-endpoint necessary condition s² + (y+√(a0²−x²))² ≤ U² gives s ≤ U, and
equality there forces x = a0, y = 0, s = U, i.e. h1 = (−e0,0),
h2 = (a0+U, 0) = (1−U, 0) with |h2| = 1−U exactly — a tangency to S¹, i.e. h2
is boundary-active, not strictly inactive, so the triple is not a legal k10
triple (exact identity: a0 + U = (1−2U) + U = 1−U). Hence legal k10 triples
have s < U strictly, the entire face d ≥ 2U (i.e. s ≥ U) is empty of legal
triples, and the root box's own s = U face — which the DFS does contain —
matters only as an illegal superset, exactly as recorded on the interface.
This also removes any tangency worry in the chart: for boxes touching s = U the
retention thresholds use s_lo, and only *legal* triples (s < U) ever need the
transversality argument of (5).

**(4) Duplicates and tangency — covered at every place they can occur.**
Repeated centers: two disks at the same center are counted with multiplicity in
k (active count) and their arcs contribute with multiplicity in Σ α_i ≥ π, so
both the classification and C986/C998/C999 (whose calibers explicitly allow
repeats) remain valid; two coincident *hubs* give d = 0, which lies in the
near-merge branch C999. Tangency: disks tangent to S¹ are active (used in the
monotonicity argument and in C986's caliber); two hub circles with 0 < s < U
meet transversally (distinct centers, equal radii); the tangent case s = U is
not in the legal chart by (3). Coincident atoms keep their multiplicities in
the demand measure, which is what the weighted union bound requires.

**(5) Exposed-atom necessity — verified, including the n1+n2 perturbation.**
For a retained hub-1 atom A = h1+Uv with |A − h2|² − U² = 4s(s−Uv_x) ≥ 0
(uniformly over a hub box because Uv_x ≤ s_lo ≤ s):
 * strict case |A−h2| > U: moving A radially outward from h1 increases
   |·−h1|; the distance to h2 changes continuously and stays > U for small
   moves, and the point stays in int D because |h_j| + U < 1 (inactive hubs), so
   A is a limit of points outside both closed hubs and inside D;
 * equality case |A−h2| = U with 0 < s < U: the outward unit normals
   n1 = (A−h1)/U, n2 = (A−h2)/U satisfy n1·(n1+n2) = n2·(n1+n2) = 1 + n1·n2,
   which is strictly positive iff n1 ≠ −n2; antipodality would force
   A to lie between the centers at distance U from both, i.e. 2s = 2U, i.e.
   s = U, excluded by (3). Hence u = n1+n2 is a direction increasing *both*
   distances simultaneously, and a small step along u (plus the int-D margin)
   exhibits A as a limit of points outside both closed hubs; the exposed-arc
   version of the argument is the same statement.
 * Since the ten ring disks are closed and must contain all points of D outside
   both hubs, their union contains the closure, hence A. Boundary atoms on S¹
   are necessary because neither inactive hub reaches S¹. Multiplicities are
   retained. The certificate's demand is therefore genuinely forced for every
   legal triple in a box, which is exactly the necessity the pigeonhole step
   (10 · (per-ring upper capture) < T) consumes.

## Sharpness notes (no gap claimed, but worth pinning)

 * **r* < U: an exact comparison of the isolating box.** By C985's certificate
   (`evidence/root-t-certificate.json`) the system F=G=H=T=0 has a unique root
   in the stated exact rational box, established by an exact rational Banach
   contraction; r* is the r-coordinate of that root, i.e. r* is defined by the
   exact root and not by any finite decimal display. The certificate also
   records that the exact root lies in the certified image of the box, whose
   r-interval is narrower than the input box, but the comparison below uses the
   ORIGINAL input box, so no property of the image beyond containment is needed.
   The r-interval of that input box is
       [18055148187225432205654385100803259/(5·10^34),
        18055148187225432205654385100903259/(5·10^34)]
   (halfwidth 10^-30), and its upper endpoint satisfies, exactly,
       U − (box upper) = 1425191629594296741/(5·10^34)
                       ≈ 2.85038325918859e-17 > 0.
   Since the root lies in the closed box, this gives the positive lower bound
       U − r* ≥ 1425191629594296741/(5·10^34) ≈ 2.85038325918859e-17 > 0,
   which is what the chain's "r < r* ⟹ r < U" and the strictness of the
   enlargement consume. Note the direction: containment in a closed box yields
   U − r* ≥ (a positive rational), not a strict inequality in r*, and no
   assertion is made here about whether r* is rational (an algebraic root need
   not be irrational without an irreducibility proof, which is not part of the
   inputs). Recorded because it is the thinnest inequality in the chain; note
   also that a displayed decimal for r* defines nothing.
 * **Constants used.** a0 = 1−2U ≈ 0.2777941, e0 = 3U−1 ≈ 0.0833089,
   1−U−1/20 ≈ 0.5888966, 4U−1+2·(1/20) = 0.5444300… < 1 (the near-merge
   containment inside int D), d = 1/10 = 0.1 < 2U = 0.7222059… (the near-merge
   and chart regimes are separated) — all exact rationals.
 * **Branch separation.** The chain's three hub regimes are d ≤ 1/10 (C999),
   d ≥ 2U (empty of legal triples, (3)), 1/10 < d < 2U (the box). No regime
   boundary needs a separate certificate: the box is closed and contains
   s = 1/20, and the d ≥ 2U regime is empty, not merely certified.
 * **Atom count / partition responsibility.** The pigeonhole argument needs the
   per-cell bound for *every* legal ring center; the dyadic discard is safe
   because a legal ring center has norm² ∈ [(1−U)², 1−U²]. This is the atomic
   kernel's obligation and is not re-audited here.

## Falsifiers of the closure

The implication would fail if any of the following were exhibited: a legal k10
triple outside the declared root box; a retained atom at a legal triple that is
not in the closed ring union; a k9 configuration with r < r*; a radius-U
configuration with 11 active disks; a radius-U k10 configuration with
d ≤ 1/10; a legal k10 triple with s ≥ U; or a box of the root domain left
unresolved while the interface is declared complete. Each of the first six is
excluded by one of the inputs or by the exact arguments above; the seventh is
the stated premise. Conversely, finding any of them would break the chain at a
*different* step, which is why the chain is stated stepwise.

Status: conditional closure verified; the single premise is the conjunction
(i)–(iv) of step 9 — empty stack, complete exact canonical partition, validated
infeasible leaves, integer-replayed atomic leaves. It is an execution and replay
obligation, not a gap in the implication, and it is not discharged by an empty
queue alone.
