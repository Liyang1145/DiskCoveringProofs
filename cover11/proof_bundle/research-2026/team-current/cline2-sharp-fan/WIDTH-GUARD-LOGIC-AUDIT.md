# WIDTH-GUARD-LOGIC-AUDIT.md — is the mean-value guard logically sufficient?

Owner: cline2-sharp-fan. Read-only inspection of `lead/interval_joint_patch.py` and
`lead/interval_patch_fibers.py` (domain C849). Own files only; no claim registered.
Question asked: do  dd_lower >= min^2,  dd_upper <= (r^2)_lower,  orient_lower > 0,
lc_lower > 0  (on the SAME (r,b,w) box)  ensure that the center sector clamps are
inactive for all outer parameters and the whole w-segment, hence that the mean-value
tightening is valid?

================================================================================
1. WHAT THE CLAMPS IN `sector()` ACTUALLY ARE  (interval_joint_patch.py lines 32-48)
================================================================================
`sector(r,s,b,w,ii)` builds v0 = P0(w) - c, v1 = P1 - c and then applies EXACTLY
three operations that can change the value:
  (C_d)  d2 = clip(dot(v0,v0), (R*I(19)/100)**2, r*r)      # None => reject
  (C_o)  orient = cross(v0,v1);  if orient.b < 0: return None;  orient = pos(orient)
  (C_l)  lc = cross(chord, back); if lc.b  < 0: return None;  lc   = pos(lc)
Everything else is a smooth function of these: orient/2, (w - sin w)/2, -mu*alpha with
alpha = atan2(orient, dot(v0,v1)), quad_range(-d,-dl,u) with u = sqrt(d2)/R, and
h*(L+w/2) with L = atan2(pos(lc), dot(chord,back)).
So the "analytic continuation" that the mean-value step needs is the evaluation with
(C_d), (C_o), (C_l) all INACTIVE (identity), for every (r,b) in the outer box and every
w in the segment.

================================================================================
2. THE GUARD IN `widthbound` TESTS EXACTLY THOSE THREE, ON THE SAME BOX
================================================================================
Lines 25-32 recompute, with formulas identical to `sector`'s:
   cx = s-2 r sb cb ; cy = -2 r sb^2
   px = s cos w - r sin w ; py = -s sin w - r cos w      (= P0(w), same as sector)
   dd     = (px-cx)^2 + (py-cy)^2                        (= dot(v0,v0))
   orient = (px-cx)(-r-cy) - (py-cy)(s-cx)               (= cross(v0, P1-c))
   lc     = chordx(cy-py) - chordy(cx-px)                (= cross(P1-P0, c-P0))
and it refuses the tightening iff
   dd.a < ((R*I(19)/100)**2).b   OR   dd.b > (r*r).a   OR   orient.a <= 0   OR   lc.a <= 0.
Because these are interval evaluations on the SAME (r,b,w) box that feeds center and
grad, passing the guard means, for ALL (r,b) in the outer box and ALL w in the segment:
   dd subset [(R*19/100)^2 , r^2]   (clip (C_d) is the identity)
   orient > 0 strictly              (no None, pos() is identity, alpha in (0,pi))
   lc > 0 strictly                  (no None, pos() is identity, L in (0,pi))
   and dd >= (R*19/100)^2 > 0  =>  u >= 19/100 > 0, so 1/u in `grad` is finite.
Hence on guard-passing boxes:
   * `center = sector(r,s,b,mid,ii)` returns the UNCLIPPED value, and since it is
     evaluated at the point w = mid with the outer boxes still interval-valued, it is a
     valid enclosure of F(mid) over the whole outer box;
   * the analytic branch is fixed (alpha in (0,pi), L in (0,pi), u > 0) so the
     derivative identities used in `grad` hold:
        (total sector area)' = (1 - c.P)/2 ,  alpha' = (1 - c.P)/d^2 ,
        (L + w/2)' = 1 - alpha' ,  (u^2)' = -2 cross(c,P)/R^2 ,
     and the assembled
        grad = (1-cp)(1/2 + (-mu-h)/dd) + h + (2 d + dl/u) xx / R^2
     is the true derivative (independent symbolic verification of these four identities
     and of the assembly was done in the previous round: A1-A3 exact, A4 by hand);
   * therefore for fixed (r,b) the mean value theorem gives
        F(w) - F(mid) in grad * (w - mid),   w in [w.a,w.b],  mid in the segment,
     and intersecting with `raw` keeps a valid enclosure.
ANSWER: YES — with the strict reading above, the guard is exactly the domain-of-validity
test of the analytic sector function on that box, so the mean-value tightening is valid
on guard-passing boxes. Two refinements, no gap:
   (i)  the guard's upper test uses (r*r).a while the clamp uses (r*r).b, so it is
        STRICTER than necessary: it may refuse boxes the clamp would have left alone.
        Conservative, not unsound.
   (ii) `mid = I((float(w.a)+float(w.b))/2)` always lies in [w.a,w.b] (binary average of
        the endpoint floats), so F(mid) is evaluated inside the segment — required by
        the MVT and satisfied.

================================================================================
3. WITHDRAWN (lead ruling) — G1 and G2 of the first version of this file
================================================================================
G1 ("the fallback `return raw` is not covered by the guard") and G2 ("evaluate calls the
same sector with no guard") are WITHDRAWN as invalid.  Lead's ruling, accepted:
  * the sector interval encloses the sector function on the ACTUAL FEASIBLE patch set
    inside the box, where lc >= 0, orient >= 0 and the distance bounds hold BY GEOMETRY;
    intersecting with that necessary range is STANDARD INTERVAL CONSTRAINT CONTRACTION
    (the box is restricted to the feasible subset), so no sign-monotonicity assumption is
    involved and not enclosing unphysical parameter points is INTENTIONAL, not an
    under-estimate;
  * the mean-value step is the only place that must extend over ALL outer parameters of
    the whole segment, and that is exactly what the guard tests; the `raw` fallback needs
    no guard;
  * the coefficient signs I quoted came from the older `joint_patch_frozen_v2.json`, not
    from the current `joint_nested_frozen.json`, so the clamp-direction discussion did not
    apply to the current certificate in any case.
Nothing else in this file depended on G1/G2; the guard proof (section 2) stands.

================================================================================
4. UNSQUARED DERIVATIVE IDENTITIES — MACHINE-VERIFIED EXACT (audit completed)
================================================================================
All four identities behind the derivative formula that `grad` uses are now verified as
EXACT polynomial identities, reduced by polynomial division modulo the only two
constraints (P1 on the unit circle: P1x^2+P1y^2 = 1; cos^2 w + sin^2 w = 1), with
P(w) = R(-w)P1, v0 = P-c, v1 = P1-c, orient = cross(v0,v1), dot1 = v0.v1, d^2 = v0.v0,
u = |v0|/R, lc = cross(P1-P, c-P), L = atan2(lc, (P1-P).(c-P)), alpha = atan2(orient,dot1):
   id0  dP/dw = -J P                                        (J = 90 deg CCW rotation)
   id1  alpha' = (1 - c.P)/d^2                              reduced remainder 0
   id2  (orient/2)' = cos w - c.P, i.e. (triangle area)' = (1-c.P)/2 - (1-cos w)/2
                                                            reduced remainder 0
   id3  (u^2)' = -2 cross(c,P)/R^2                          reduced remainder 0
   id4  (L + w/2)' = 1 - alpha'                             reduced remainder 0
Hence, by linearity, the assembled
   F' = (triangle area)' + (w - sin w)'/2 - mu alpha' - d (u^2)' - dl u' + h (L + w/2)'
      = (1-p)[1/2 + (-mu-h)/d^2] + h + (2d + dl/u) cross(c,P)/R^2
is the exact derivative, i.e. exactly the expression coded as `grad`.
(An earlier run of `tools/a4_identities.py` printed False for id1/id2/id4: that was a
harness defect — a typo "+1" in the id2 test string and an incomplete reduction of the
id1/id4 polynomials.  Both are fixed; the corrected checks give 0 for id1, id2 and id4,
and an independent dps=30 numeric check at a generic point agrees to 1e-19.)


================================================================================
4. SUMMARY (logic only)
================================================================================
* Guard-passing box: clamp-free analytic evaluation; center valid; MVT valid; the
  intersection with raw is valid.  The asked implication HOLDS.
* Guard-failing box: the code falls back to `raw`, which is only a valid upper bound for
  the dd- and orient-clamps (given the current coefficient signs) and can be an
  UNDER-estimate for the lc-clamp; therefore "guard fails" must mean "refine/reject",
  not "use raw", for the certificate to be sound.
* The same clamp structure exists in `evaluate` without a guard.
