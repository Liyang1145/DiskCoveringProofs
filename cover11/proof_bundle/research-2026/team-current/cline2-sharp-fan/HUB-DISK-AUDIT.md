# HUB-DISK-AUDIT.md — review of HUB-CONVEX-LENS-REDUCTION.md + CARTESIAN-HUB-DISK-INTERSECTION.md

Owner: cline2-sharp-fan (own files only; no kernel write, no lead edits).
Instrument: tools/hub_disk_audit.py + a clean symbolic re-run -> out/p37_hub_disk_audit.txt.
Scope of this review: DOMAIN and EQUIVALENCE of the C848 hub set only (not objective convexity).

VERDICT: every structural claim in the two notes is CORRECT.  Two clarifications are worth
recording (one logical dependency in the convexity claim, one dropped root in the disk form);
neither changes a statement, both make the "EXACTLY" claim airtight.

================================================================================
1. THE DISK FORMS (all verified as exact identities, residuals 0)
================================================================================
With v = H cos delta, t = H sin delta, c9 = (s-v, -t), A = b1-delta, B = b2+delta, s = sqrt(1-r^2):
 (i)   hub-norm  |c9| <= 1-r   <=>  (v-s)^2 + t^2 <= (1-r)^2
                    <=>  H^2 - 2 s H cos delta + 2r(1-r) <= 0            [residual 0]
 (ii)  face 1  H <= 2r sin(2b1-delta)   <=>  (v - r sin2b1)^2 + (t + r cos2b1)^2 <= r^2
                                                                          [residual 0]
 (iii) face 2  H <= 2r sin(2b2+delta)   <=>  (v - r sin2b2)^2 + (t - r cos2b2)^2 <= r^2
                                                                          [residual 0]
       (proof is just completing the square after multiplying by H > 0; in the (v,t) frame the
        hub IS the point (v,t) and each disk centre C satisfies |C| = |C - c2| = r, so for any
        point of the disk  H = |(v,t)| = |c9 - c2| <= |(v,t) - C| + |C| <= r + r = 2r:
        the explicit H <= 2r constraint IS automatic, as stated.
        [TYPO CORRECTED per lead: H = |(v,t)| = |c9 - c2|, NOT |c9|; conclusion unchanged.])
 (iv)  separation  H^2 >= 2 r |t|  <=>  v^2 + (|t| - r)^2 >= r^2  <=>  BOTH disk exteriors
                    v^2 + (t-r)^2 >= r^2  and  v^2 + (t+r)^2 >= r^2   [exact, min form = 0]
 (v)   legal wedge  -b2 < delta < b1  <=>  v > 0 and -v tan b2 < t < v tan b1  [exact]

================================================================================
2. REDUNDANCY OF THE SEPARATION BOUND — CORRECT, AND PROVED TWO INDEPENDENT WAYS
================================================================================
Geometric: |(0,+-r) - (s,0)| = sqrt(s^2+r^2) = 1 = (1-r) + r, so the hub disk B((s,0),1-r)
and the two endpoint disks B((0,+-r), r) are externally tangent; for X in the hub disk the
reverse triangle inequality gives |X-(0,+-r)| >= |(0,+-r)-(s,0)| - |X-(s,0)| >= 1-(1-r) = r,
i.e. X satisfies both exteriors, i.e. H >= 2r|sin delta| holds automatically.
Analytic: |P+- - c9| >= 1 - |c9| >= r for the unit-boundary points P+- = (s,+-r) (|P+-| = 1),
and |P+- - c9|^2 = v^2 + (t -+ r)^2 (up to sign): exactly the two exteriors.
Validity: all r in (0,1) — no domain restriction, no ridge assumption, no numerics.
Tangency: (v,t) = (s,0) + (1-r)((0,r)-(s,0))/1 = (r s, r(1-r)) (and its mirror) — matches the
note.  At those points the exterior constraints hold with EQUALITY; they are the only such
points of the hub disk.

================================================================================
3. CONVEXITY — CORRECT, WITH ONE DEPENDENCY TO RECORD
================================================================================
C848 hub set (fixed r,b1,b2) = (two face disks) INTERSECT (hub-norm disk) INTERSECT (wedge).
All three disks are closed and convex; the wedge is an open sector {v>0, -v tan b2 < t < v tan b1}
of angle b1+b2 < pi, also convex.  Hence the intersection is convex, and its closure compact
convex — as the first note says.
RECORDED DEPENDENCY: the second note describes the same set as "three closed disks, OUTSIDE two
other disks, within the wedge".  Read literally, that description is NOT convex (complements of
disks are not convex); convexity holds precisely BECAUSE the two exterior conditions are
redundant (section 2).  So convexity of the C848 hub set is a consequence of the redundancy
theorem, not an independent fact — worth one cross-reference line between the two notes.

================================================================================
4. FACE CIRCLES, INTERSECTIONS AND THE RIDGE — CORRECT
================================================================================
Centres C1 = (r sin2b1, -r cos2b1), C2 = (r sin2b2, r cos2b2) (both norm r, so both circles pass
through the origin = c2):
 * |C1 - C2|^2 = 4 r^2 cos^2 T  exactly  [residual 0], T = b1+b2 — the note's centre-distance
   formula (this is the cosmetic "4r^2cos^2T" claim).
 * midpoint M = (C1+C2)/2 has |M|^2 = r^2 sin^2 T.
 * the radical axis is {X : X.(C2-C1) = 0} (because |C1| = |C2| = r), hence passes through the
   origin; the two circle intersections are therefore 0 and 2M = C1+C2 =
   (2r sinT cosD, 2r sinT sinD), D = b1-b2 — exactly the note's (v*,t*).
 * that point lies on the ray delta = D, so H = 2r sinT = 2r sin(b1+b2) — the ridge point.
   Its strict containment in the hub disk is the theorem proved in C853-RIDGE-UNIFORM.md
   (norm < 0 with true slack ~7.6%), and being outside the forbidden disks is automatic
   (section 2).  So "ridge = unique non-origin intersection, feasible" is confirmed.
 * T = pi/2: |C1-C2| = 0, and indeed sin2b1 = sin2b2, cos2b1 = -cos2b2 hold exactly there, so
   the two face disks coincide and impose no independent constraint.  The ridge point
   (2r cosD, 2r sinD) is still well defined and feasible.  Convexity is unaffected.

================================================================================
5. MINOR CLARIFICATIONS (no error, but needed for the word "EXACTLY")
================================================================================
 (a) DROPPED LOWER ROOT.  The disk form of a face constraint encodes only the upper root
     H <= 2r sin(2b1-delta) = 2r sin(b1+A).  The coded C848 face condition is the full
     quadratic, i.e. H in [2r sin(b1-A), 2r sin(b1+A)] = [2r sin delta, 2r sin(2b1-delta)].
     So "three disks" drops the lower root H >= 2r sin delta.  That is legitimate — and it is
     exactly the redundancy: the hub-norm disk gives H >= 2r|sin delta| >= 2r sin delta, so the
     lower root is automatic.  The chain therefore closes:
        three disks + wedge  =>  hub-norm  =>  separation  =>  lower roots  =>  full C848 set,
     which is what makes "the C848 hub set is EXACTLY the intersection of three disks and the
     wedge" true.  (This is the same content as the C856 statement that the hub-norm angle cap
     acos q implies |delta| <= asin(H/2r).)
 (b) "AT MOST THREE INTERVALS" IS SAFE BUT NOT SHARP.  The three chord intervals listed in the
     second note are the correct t-sections of the three disks, and their intersection is one
     closed interval.  Removing the two exterior intervals cannot split it, because those
     intervals are already disjoint from the hub disk (section 2).  So the sharp statement is
     "fixed v gives one closed interval", which is what the first note asserts; the "at most
     three" of the second note remains true and is harmless as a relaxation.
 (c) v LOWER BOUND.  v >= s - (1-r) follows from the hub disk, and s-(1-r) > 4r/5 on
     [3/8, 19/50]: f(r) = sqrt(1-r^2) - 1 + r/5 is decreasing there, f(19/50) = sqrt(2139)/50 -
     231/250 = 0.0009865 > 0.  [SHARPER EXACT FLOOR per lead: the same quantity is
     sqrt(2139)/50 - 231/250, and positivity follows from the single integer comparison
     25*2139 = 53475 > 53361 = 231^2; my earlier equivalent form 2 sqrt(2139) > 81 <=> 8556 > 6561
     is also valid but weaker.  Both are exact rational comparisons.]  Confirmed, with the
     minimum at r = 19/50 (so the bound is tight-ish but valid).

================================================================================
6. WHAT THIS DOES NOT SAY
================================================================================
The notes' own scope statements are correct and I confirm them: the reduction removes a
non-convex constraint class from C848 (the separation exteriors) and gives an exact Euclidean
chart (r,b1,b2,v) + t, but it asserts NOTHING about convexity or concavity of the objective and
nothing about the maximum being attained at the ridge or on the intersection points.  That is
consistent with the earlier rounds' findings (F_H is neither concave nor convex in general, and
the unconstrained H-argmax can be interior).

STATUS: audit complete, all claims confirmed, two clarifications recorded.  No claim registered.
