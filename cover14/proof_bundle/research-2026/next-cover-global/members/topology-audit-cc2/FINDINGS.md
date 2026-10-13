# Findings — topology-audit-cc2 (independent audit of the k10 cover→dual→catalogue chain)

> **CORRECTIONS (this file is append-only; the items below supersede parts of it):**
> * **F5 is WITHDRAWN in full as a counterexample** (see also F5 note below): the strictly
>   tangent site used by probe Z2 is NOT a legal cover (Z3: covering radius ≈0.735 >> U), and the
>   "no singleton owner" and "3-ring face excluded" corollaries I derived from it are FALSE
>   (singleton ownership can occur at a tie under non-strict nearest ownership; {i−1,i,i+1} is a
>   legitimate pairwise-adjacent triple in C11). Only the full-cell lemma below survives.
> * **F3 is WITHDRAWN** (my hub-facet-midpoint counterexample placed hubs ON S^1, illegal for
>   inactive hubs, and the discriminant identity I used requires exactly that).  See
>   `SECTION2-FULL-CELL-LEMMA.md` §0.
> * **F5(a),(b) are WITHDRAWN** as counterexamples: the strictly-tangent site used by probe Z2
>   is NOT a legal cover (its covering radius far exceeds U — Z3), so the ownership jump it
>   shows is irrelevant.  F5's observation that the lead's one-line strictness derivation
>   needed the equal-norm case is kept as a MINOR correction only (equal norms give d=0).
> * **The §2 full-cell lemma is TRUE** in its narrowed form; I now have an independent proof
>   (`SECTION2-FULL-CELL-LEMMA.md` §1): a cell whose S^1-intersection is empty is compact inside
>   the OPEN disk (so the outward clip kills it), while a tangential singleton is possible only
>   as an ownership tie, which is exactly why the clip is necessary.  Claim C1170.
> * **F0/F1/F2**: F0 and F2 stand; F1's criticism of the canonicalisation is WITHDRAWN for the
>   current generator (which uses sh − v and passes invariance) and applies only to the old file.

Scope of every item: n14, 0<r<=U=.33173203427623414, k=10 branch, after same-arc inner-root
normalization. Route commandcode2/deepseek/deepseek-v4-flash. Nothing here is a metric
exclusion; all items are about I1-I5 of AUDIT-PLAN.md.

## F0 (instrument calibration, PASS) — independent re-enumeration reproduces the catalogue

`enum_indep.py` re-derives the whole finite list from scratch, importing NOTHING from
`members/topology/gen_k10_catalogue.py`:
all connected hub graphs by brute force on 2^(m(m-1)/2) edge sets; forced hub-only-triangle
count h=e-m+1 (re-derived from V-E+F=1); hub multigraph with multiplicity 2-h_e; ALL Euler
circuits; all weak compositions into N links; faces built from the walk; validity by an
independent simplicial-disk test (distinct vertices, edge incidence 1 on the N ring edges and 2
elsewhere, connected vertex links with degree-2 hubs / two-ended-path rings, chi=1).

| object | my raw valid complexes | my distinct classes | stored list | stored distinct classes | set equality |
|---|---|---|---|---|---|
| n12 N=9 m=3 | 262 | 51 | 51 (nine-topology/graphs.json) | 51 | **YES** |
| n14 N=10 m=3 | 348 | 68 | 93 (k-catalogue-n14 10/3) | 68 | **YES** |
| n14 N=10 m=4 | 21084 | 932 | 1442 (k-catalogue-n14 10/4) | 932 | **YES** |
| lead corrected 10/3 | — | 68 | 68 | 68 | **YES** |
| lead corrected 10/4 | — | 932 | 932 | 932 | **YES** |

**Also verified:** a faithful replica of the CURRENT generator's canonicalisation
(`lead/gen_k10_fixed_copy.py`, reflection v ↦ sh − v) is a genuine group invariant
(0 violations over 3240 transformed paths) and yields the same 68 classes as my independent
canonicalisation. The old `members/topology/gen_k10_catalogue.py` uses v ↦ 2sh − v and is NOT
invariant; that file's diagnosis is unchanged.

Canonicalisation used here is `canon_true` (canon_check.py): minimum over the FULL group
D_N x S_m, i.e. all 2N ring maps v -> eps*v+sh together with all m! hub permutations.
Invariance was TESTED, not assumed: for every sampled class, canon_true is unchanged under all
2N*m! group elements (0 violations). The same test applied to a faithful replica of the lead's
`full_canon` shows 30-90 violations per sampled class, i.e. the lead's canonical procedure is
NOT a group invariant (harmless for the final count here, because the minimum over a full group
orbit is invariant whenever the orbit is complete — see F1).

Evidence: `evidence/indep-enum-N9-m3.json`, `-N10-m3.json`, `-N10-m4.json`,
`evidence/compare-stored.json`, `evidence/canon-test-N10-m3.json`.
Repro: `py -3 -B enum_indep.py 10 4` ; `py -3 -B canon_check.py 10 3` ; `py -3 -B compare_stored.py`.

Consequence: interface I4 (Euler-walk enumeration completeness) and I5 (canonical count 1000 =
68+932) are independently CONFIRMED at the level of "the retained set is exactly this". The
overcount claim 1535 -> 1000 is confirmed (the 1535 stored entries carry exactly 68 and 932
distinct classes). A second, independent calibration is the odd-N n12 case: my from-scratch
enumeration gives 51 classes for N=9 m=3, i.e. the same odd-N count as the n12 type list, so
this is not a parameter accident.

## F1 (WITHDRAWN — method note corrected)

My claim that "the lead's full_canon is not a group invariant" belongs to the OLD
`members/topology/gen_k10_catalogue.py` (reflection v ↦ 2sh − v, 30–90 invariance violations
per sampled class). The CURRENT generator `lead/gen_k10_fixed_copy.py` uses the correct
reflection v ↦ sh − v; a faithful replica of its `full_canon` passes my invariance test with
0 violations over 3240 group-transformed paths and yields the same 68 classes as my independent
canonicalisation. So: F1's criticism is WITHDRAWN for the current code; only the old file is
affected. The conclusion of F0 stands unchanged.

## F2 (data hygiene) — `members/topology/k10-catalogue.json` carries an EMPTY catalogue

`k10-catalogue.json` has `catalogue_size: 0`, `entries: []`, and
`raw_checked_items_per_skeleton` all zero, while the 1535 stored entries live in
`k-catalogue-n14.json`. Any consumer that reads "the k10 catalogue" from the file with the
obvious name gets nothing. Low mathematical risk, real interface risk.

## F3 (GAP in the audit's collar proof) — a hub facet midpoint CAN lie on gamma

`lead/K10-CATALOGUE-AUDIT.md` asserts "all hub cells, all hub site and every non-ring dual edge
are inside gamma" and `COVER-TO-DUAL.md` Lemma C assumes the two spoke halves lie on distinct
spoke lines "using c_i not in either spoke line". That genericity is FALSE:

Let ring site c_i and two hubs h1,h2 satisfy (a) |c_i h1| = |c_i h2| and (b) |h1 h2| =
2*|c_i h1| - 2r, i.e. h1,h2 are the two tangency points of B(c_i,r) to S^1. Then h1h2 is
perpendicular to c_i (perpendicular bisector) and half its length is |c_i h1| - r. Put
q = h1 + ((h1h2)/2). Then dist(h1,q) = |c_i h1| - r = dist(h1,c_i) - r, so dist(q,c_i) = r,
hence q is ON S^1 and equidistant (r) from c_i,h1,h2, so q is the midpoint of the hub-hub
facet and simultaneously the midpoint of the spoke facet S^1 ∩ V_{c_i} ∩ V_{h1}. The ray from
h2 towards q is then BOTH the dual edge to the hub-hub facet and the dual edge to the spoke
facet: two distinct facets of the same cell with the same midpoint and the same first segment,
so the "distinct facets give distinct rays" step of Lemma A fails, and gamma passes through q
with both hubs touching gamma.

Why this is a gap and not (yet) a counterexample: (i) realizability of such a configuration
while D is covered at radius r and inner-root normalization holds is not established here — a
finite search is in `probe_degenerate.py`; (ii) even when it occurs, the bounded region still
appears to be a disk whose boundary merely TOUCHES the hub cells at q, so the disk conclusion
survives, but the proof as written does not exclude it and the strict-interiority statement is
false. The correct statement to prove is "no hub cell has interior meeting the collar sectors",
not "hub cells are strictly inside gamma". Where a legal cover with that degeneracy exists the
dual-disk is still a disk but its dual graph is not the fan graph: the hub-hub facet and the
spoke facet are not separately dualised. See F5 for the effect on the catalogue.

## F5 (WITHDRAWN as a counterexample; superseded by C1170)

**[This section is kept only as a record. Its counterexamples were shown to be illegal
configurations and its two derived corollaries are FALSE; see the header note and
SECTION2-FULL-CELL-LEMMA.md.]**

Lead's proposal (messages of this round): replace actual-arc essentiality by
"q = number of POSITIVE-LENGTH nearest-owned boundary arcs Ji is 10 or 11"; then the same
short-arc J = S^1 ∩ B(p,2r) measure argument gives no-chord for owner disks with cyclic
distance >= 3 (q=11) / >= 2 (q=10), and the remaining non-owner sites are treated as interior
nodes (possible "hidden active" sites whose Ji is a singleton at a ring switch), plumbed by a
virtual ring edge through the boundary triple point x with witness x <= r.

Assessment (independent):
 (a) The strict bisector lemma d<s IS correct: for distinct centres with norms <= s=sqrt(1-r^2),
     d = | |cj|^2-|ci|^2 | / (2|cj-ci|). If norm_i = norm_j then d = 0. Otherwise
     d <= (norm_i+norm_j)/2 and, unless both norms are equal to s, at least one is < s; if both
     equal s then d = 0 again. In every case d < s, hence the two S^1 crossings of the bisector
     are separated by > 2 asin r > |actual arc| (the halfwidth bound is STRICT unless the centre
     is at the outer root, where the arc is a singleton). So at most one crossing lies in any
     single actual arc, and each pair's non-strict nearest constraint cuts A_i to a single
     interval or nothing. This does NOT need essentiality. VERIFIED (analytic; the equality
     case norm_i=norm_j=s gives d=0, which the lead's sketch got backwards — it wrote
     "d<=(normi+normj)/2<s because at least one norm<s, else both norms equal" and then needed
     d< s; the correct case split is as above).
 (b) The claim "q=10 or 11, each Ji positive length" is FALSE as stated: a hidden active site
     (disc of radius r meeting S^1 in exactly {x}, cell of positive area inside S^1) has
     Ji = {x}, a singleton of zero length, and it is a boundary TRIPLE-owner at the ring switch
     x: the two neighbouring positive owners also pass through x (coverage at x, nearest
     distance <= r). So the lead's own "hard点" is real and is not removed by the strict lemma.
     The counted family is therefore q = 10 positive owners PLUS an arbitrary number of
     singleton owners, i.e. the sweep of S^1 by positive-length owned intervals does not even
     determine the ring order (a singleton has no interval to order), so the lead's "positive
     OWNER count replaces active count" does not close.
 (c) Independent confirmation that a hidden cell need not lie inside D follows from the
     lead's own convexity argument being incomplete: for a CONVEX cell with an interior site
     strictly inside D touching S^1 at exactly one point x, the cell can still have nonempty
     portion outside D (e.g. take the cell to be a closed half-plane bounded by a line with
     d(0,line)=1 tangent to S^1; the cell touches S^1 only at x yet is half outside D). What the
     convexity argument really needs is that the OUTSIDE portion is covered by other cells,
     which is automatic under coverage of D but does not force the cell inside D. So "enlarge
     and kill" is not immediate; the epsilon-clip proposal needs its own proof that the
     positive-owner set and the no-chord margin survive the enlargement at r+eps -- the margin
     at r<=U is asin(2r)+7asin(r) < pi by only +2.8 degrees, so an eps-enlargement is NOT
     margin-free: one must rerun the constant comparison at r+eps, which is exactly the
     quantity that is thin at U.
 (d) Even granting the virtual-edge plumbing, the resulting combinatorial family is NOT the
     1000-list: a ring-ring virtual edge through a boundary triple point creates a dual edge
     between two ring sites that may be non-adjacent (the two positive owners adjacent to a
     hidden site are both adjacent to it, hence adjacent to each other in the 11-cycle only if
     the hidden site sits between them, which it does; but the virtual edge is a ring-ring
     edge not present in the fan enumeration of gen_k10_catalogue, whose build() explicitly
     rejects every non-consecutive ring pair). So the unified family must be re-enumerated.

Minimal counterexample / missing item to discharge (d): exhibit (or prove impossible) a legal
inner-root normalized n14 cover at r<=U with exactly 10 positive owners, one hidden active
site with singleton Ji, and a Voronoi cell of the hidden site extending outside D. Search is
`probe_degenerate.py`; a positive instance would falsify (K1)-style connectedness AND the
"cell inside D" step, a negative instance would need a proof.

## F4 (what this audit does NOT establish)

No metric exclusion of any of the 1000 classes is audited here. k11 is untouched (the
members/topology/k-catalogue-k11.json list has no established hypotheses). The corrections
in F0 do not upgrade the k10 bound to a global optimum; they certify only the finite list.
