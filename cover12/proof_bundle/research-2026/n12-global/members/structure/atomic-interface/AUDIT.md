# Interface audit: ATOMIC-DUAL-PROOF.md + hubline_domain.py (global wrapper)

Auditor: structure member. Read-only on lead files. Artifacts:
`members/structure/atomic-interface/{AUDIT.md,check_wrapper.py}`.
Per instruction, the atomic kernel's own upper bounds (Fraction + error-proof)
are NOT re-audited here; only the global domain wrapper, the three prune
predicates, the moving-atom necessity argument and the seams are.

Constants (exact): U = 22568935234031792038557518369/62500000000000000000000000000,
a = 1-2U, e0 = 3U-1. Exact rational values are printed by check_wrapper.py.

Branches to be sewn: (N) near-merge, d<=1/10, i.e. s<=1/20 [K10-NEAR-MERGE];
(W) wrapper, s in [1/20,U] [hubline_domain.py]; (S) separated hubs, s>=U
[ATOMIC-DUAL-PROOF prose, "excluded by separated-hub lemma"].

## Q1. Does the wrapper root box cover every legal normalized k=10 triple?

Box: s in [1/20, U], x in [0, 1-U-1/20], y in [0, e0].
YES, with the proofs below; all four faces are the exact derived bounds.

(L1) Both hubs strictly inactive: (x+s)^2+y^2 < (1-U)^2 (implies h1 because
     |x-s|<=x+s for x,s>=0).
(L2) Core K=B(0,a) covered by the hub union. Necessity of each face:
  * x <= 1-U-1/20: from (L1), x+s <= 1-U, and the wrapper's s>=1/20, so
    x <= 1-U-s <= 1-U-1/20. (Exact: 1-U-1/20 = 19/20 - U.)
  * y <= e0: the core point (0,-a) gives min_j|(0,-a)-h_j|^2 =
    (x-s)^2+(a+y)^2 <= U^2 (as |x-s|<=x+s), hence a+y <= U, y <= U-a = e0.
  * s <= U: proved in members/structure/hub-line-audit/AUDIT.md (D3/R4):
      case x>=a: (L1) gives x+s <= 1-U and x>=a, so s <= 1-U-a = U;
      case x<a: the audited endpoint condition s^2+(y+sqrt(a^2-x^2))^2 <= U^2
                gives s <= U immediately.
    Equality s=U forces (x,y)=(a,0) uniquely, i.e. h1=(-e0,0), h2=(1-U,0).
  * s >= 1/20 is not a legality bound but the seam with (N).
  * x >= 0, y >= 0 are chart normalization, not restrictions.

Exact-rational check (no sampling): at s=U, (x,y)=(a,0) one gets
|h2| = x+s = a+U = 1-U exactly, so h2 is boundary-active, NOT strictly
inactive. Hence the s=U face contains NO legal k=10 triple: legal triples have
s<U strictly. Consequently the wrapper's upper face is harmless (it may stay
pending without affecting the k=10 conclusion), and the prose's "d>=2U already
excluded" is consistent (that region is empty for legal triples).
The check script verifies the two exact identities (e0 = 3U-1, a = 1-2U), the
face identity 1-U-1/20 = 19/20-U, and the s=U computation above exactly.

Verdict Q1: OK. Only bookkeeping caveat: [1/20,U] includes the s=U face, so the
final assembly must state that this face is (i) empty of legal triples, and
(ii) either certified by the atomic run or explicitly discharged. It cannot be
silently left pending if the status is declared global.

## Q2. Are the three illegal prunes safe?

(P1) Outer-hub-inactive prune:
     normlower([xl+sl,xh+sh],[yl,yh]) > (1-U)^2.
     The left side is the exact rational lower bound of |h2|^2 over the box
     (interval square, independent of the correlation between coordinates, hence
     a valid lower bound). If it exceeds (1-U)^2 then every triple in the box has
     |h2|>1-U, i.e. h2 is boundary-active, so no legal k=10 triple lies in the
     box. SAFE. Note the strict ">" keeps the boundary |h2|=1-U (which is
     exactly the s=U, x=a, y=0 illegal point) inside the box; conservative,
     hence still safe.

(P2) Rational core-witness prune: for each fixed exact rational point
     (a c, a t) with c^2+t^2=1 (so the point lies on the core circle and hence
     in K, and is therefore within U of at least one hub for every legal triple),
     require min_j lowerbound|(a c,a t)-h_j|^2 <= U^2. If the lower bound exceeds
     U^2 for both hubs, no legal triple lies in the box. SAFE, provided:
      (a) the witness list is exact rational and on the core circle - the code
          builds (a*c, a*t) with integer/exact rational unit vectors, yes;
      (b) the distance lower bounds are computed with the coordinate intervals
          h1x=[xl-sh, xh-sl], h2x=[xl+sl, xh+sh], y in [yl,yh], which the code
          does correctly (h1's x-interval is the min/max of x-s over the box).
     No other hypothesis is used: h1x above is exactly the reachable range of
     h1's x-coordinate, so the interval bound is valid for every triple in the
     box. SAFE.

(P3) Bisector-endpoint prune, only when xh<a:
     interval lower bound of s^2 + (y + sqrt(a^2-x^2))^2 > U^2.
     When the whole box has x<a, the audited exact core criterion (case
     0<=x<a) requires s^2+(y+q)^2 <= U^2 with q=sqrt(a^2-x^2); a strict lower
     bound above U^2 therefore refutes every triple in the box. The code uses
     directed sqrt bounds of a^2-x^2 on [xl,xh] (mapping x -> sqrt(a^2-x^2) is
     decreasing, so the outward bounds are [sqrt(a^2-xl^2), sqrt(a^2-xh^2)]).
     The guard xh<a keeps the case condition uniform over the box, which is
     conservative: boxes straddling x=a are retained and must be certified.
     SAFE.
     Note the prune is *not* available for boxes with x>=a (there the criterion
     is |h1|<=e0 instead); the code correctly does not use it there.

Verdict Q2: all three prunes are necessary-condition prunes and safe. No prune
uses a numeric LP acceptance; the code's `propose` gate only skips attempts, and
acceptance requires the atomic certificate's `status=='certified'`.

## Q3. Moving retained atoms: is ring coverage necessitated correctly?

The demand is: every retained atom is covered by the ten ring disks (the two
hubs are the only other disks, so this is exactly "the atom is not in the
interior of the hub union", in a limit sense).

Retention: hub1 atom h1+Uv, v=(c,t) rational unit, retained only if Uc<=s_lo;
      hub2 atom h2+Uv retained only if Uc>=-s_lo.
 (a) Exact identity: |h1+Uv-h2|^2 - U^2 = |Uv-2s(1,0)|^2 - U^2 = 4s(s-Uc)
     for hub1, and 4s(s+Uc) for hub2 (the document's formula). Since every
     triple in the box has s>=s_lo, the retention condition Uc<=s_lo gives
     s-Uc>=s-s_lo>=0, so the atom is outside or on the other hub. Same for
     hub2. Verified here as exact algebra.
 (b) The atom lies exactly on the boundary of its own hub, hence not in the
     interior of the hub union.
 (c) Necessity: if the atom lies strictly outside the other hub, a small move
     in a direction that increases both distances (exists unless the two
     outward vectors are antipodal; antipodality forces s=U) keeps the point
     outside both closed hubs and, because both hubs are inactive, inside
     int D; then the closedness of the finite union of ring disks applies. At
     an intersection atom of the two hub circles with s<U the circles cross
     transversally, and points of the exposed arc just outside the other hub
     approach the atom, so closedness applies again. At s=U the endpoints are
     tangency points; that face is handled separately (see Q1/atoms discussion)
     and, as shown in Q1, contains no legal k=10 triple.
 (d) Labels: retention thresholds use s_lo, so the retention is uniform over
     the box and independent of which hub carries which label; the demand is
     symmetric in the two hubs. The ring disks are the ten boundary-active
     ones, unlabelled. No label-dependent assertion is used.
 (e) Weighted Dirac masses with coincident locations are handled by summing
     weights; nothing in the necessity argument depends on distinctness.
Verdict Q3: SOUND, with the s=U tangency point as the single delicate case and
it is outside the legal k=10 class.

## Q4. Seams

 * (N)|(W): both branches include s=1/20 (near-merge d<=2*delta with delta=1/20
   closed, wrapper s>=1/20 closed). The union is all s>0, provided the
   near-merge certificate at delta=1/20 passes (that document states delta is
   yet to be certified; FLAG: the seam's validity is conditional on it).
 * (W)|(S): s=U face; per Q1 it contains no legal k=10 triple, so the region
   s>=U is empty for the class and the "separated-hub lemma" is only needed for
   the prose, not as a domain branch. FLAG: keep the two statements consistent
   (either empty-of-legal or discharged) so that "partial" status is not
   reported for an empty face.
 * Excluded middle: the wrapper's box includes illegal triples (hubs active or
   core uncovered). Per the document this is intentional and harmless: the
   atomic contradiction is derived from a necessary condition that holds for
   legal triples only, so illegality inside a box does not weaken the exclusion.
   Confirmed correct reasoning (the contrapositive: a legal triple in the box
   would force the atoms to be coverable).
 * Normalization: the chart (hub line) plus the wrapper cover x>=0,y>=0 and
   s>=1/20; the cases y<0, x<0 and d=0 are reached by reflection/label swap, and
   d=0 lies in the near-merge region. No seam is missing there.

## Flags (things I would not sign as-is)

F1. Wrapper upper face s=U is in the DFS domain but contains no legal k=10
    triple (exact: |h2|=1-U there). Either exclude it explicitly or document
    that pending status on that face does not affect the k=10 conclusion.
F2. Seam (N)|(W) at s=1/20 depends on the near-merge delta=1/20 certificate,
    which is not yet established in the documents I audited.
F3. hubline_domain.py line 53 raises RuntimeError("tiny unresolved hubbox") when
    a box of width < 1/100000 cannot be pruned or certified. That converts an
    unresolved (but possibly legal) box into a crash rather than into a pending
    leaf; for an unattended long run it risks losing the persisted queue state
    (the state is written after the loop, not in a finally block). Suggest
    pushing such boxes to `pending` with a `stuck` flag instead of raising.
F4. The docstring's "Endpoint s=U can be excluded separately by separated-hub
    theorem" and ATOMIC-DUAL-PROOF's "not already excluded by d>=2U" should be
    unified: for legal k=10 triples the s>=U region is empty (proved here), so
    the separated-hub branch is not needed as a domain branch.

## What this audit does not cover

The atomic kernel's interval bounds (referred to the independent upper-audit),
the k=9 branch, the separated-hub lemma itself, and any numeric LP acceptance
(correctly absent from the code path). No domain was deleted on the basis of a
numeric LP, and none is recommended here.

---

# Addendum (same session, after lead updates)

## A1. Status of the flags raised above

 * F1 (s=U face): CLOSED by the lead - written into the interface as "legal
   k=10 empty on s=U". This matches the exact computation in Q1 (|h2|=1-U at
   the only s=U candidate).
 * F2 (seam at s=1/20 depended on the near-merge delta certificate): CLOSED by
   C999 - all 12 near-merge segments pass and the finite-reduction
   source/inference/records audit is complete. The seam (N)|(W) at s=1/20 is
   therefore covered by two closed branches.
 * F3 (tiny unresolved box raised instead of parked): FIXED - unresolved tiny
   boxes are returned to the stack with a break, and the atomic state is saved
   every 100 boxes. No further action.
 * F4: superseded by F1/F2 closures; the s>=U region is empty of legal k=10
   triples, which is now stated on the interface side.

## A2. Simplified prune 3 (radical-free) - verified exact

New predicate when xh<a, all quantities exact Fractions:
    q2  = a^2 - xh^2
    rhs = U^2 - sl^2 - yl^2 - q2
    illegal  <=>  rhs < 0   or   4*yl^2*q2 > rhs^2 .

Verification (script `check_prune3_simplified.py`; deterministic exact boxes,
no sampling):
 (i) Exact equivalence with the monotone lower bound. For 0<=x<a the audited
     core criterion requires s^2+(y+sqrt(a^2-x^2))^2 <= U^2 for every triple of
     the box. On x in [xl,xh] c [0,a) the map x -> sqrt(a^2-x^2) is decreasing,
     so its minimum on the box is sqrt(a^2-xh^2) = sqrt(q2); with s>=sl and
     y>=yl the pointwise minimum of the left side over the box is exactly
         L = sl^2 + (yl + sqrt(q2))^2 .
     Then
         L > U^2  <=>  sl^2+yl^2+2*yl*sqrt(q2)+q2 > U^2
                  <=>  2*yl*sqrt(q2) > U^2 - sl^2 - yl^2 - q2 = rhs .
     If rhs<0 the left side is >=0 and the right side negative, so the
     inequality holds (predicate fires). If rhs>=0 both sides are non-negative
     and squaring is an exact equivalence
         2*yl*sqrt(q2) > rhs  <=>  4*yl^2*q2 > rhs^2 .
     Hence the new predicate is EXACTLY "L > U^2": no rounding, no square root,
     and the only case distinction (rhs>=0) is the first disjunct. The guard
     xh<a keeps the whole box inside case 2 of the core criterion, where the
     inequality is necessary, so the prune remains a necessary-condition prune
     and cannot remove a legal triple.
 (ii) Cross-check: on deterministic exact boxes the new predicate agrees with an
      independent 60-digit evaluation of L>U^2 in every case, including yl=0,
      q2 -> 0 (xh -> a), and sl=U.
 (iii) Edge cases: yl=0 makes 4*yl^2*q2 = 0 > rhs^2 impossible when rhs>=0, so
      the predicate reduces to rhs<0, i.e. sl^2+q2>U^2, which is exactly
      L>U^2 there. q2=0 cannot occur under the strict guard xh<a.

## A3. Run status reading

The counters quoted (2200 processed / 1021 atomic accepted / 76 illegal /
7 pending) describe a partial run: a global claim needs an empty stack plus the
F1 statement about the s=U face. The acceptance path still requires
status=='certified' from the atomic kernel, and numeric proposal values continue
to gate attempts only. No new measurement was taken for this addendum, per
instruction.
