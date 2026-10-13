# Lead audit: C1355 effective first-exit localization

Read member report/script and bearing local-directional-box proof. Reran diagnostic and checked exact kappa>.00417605, final squared displacement<(5.27e-8)^2 separately using Fraction. No independent AD/KKT recertification claimed.

Bearing checks:
- Symmetric W^T HessP W has eigenvalues>=1-b from the weighted row majorant. ||W||²<=B gives HessP>=(1-b)/B I. Invertibility is inherited from C1262 exact replay.
- Multipliers sum1, not18. For delta<=0, 2lambda+3delta>0 implies lambda delta+1.5delta²<=0. For delta>0 use delta<=h. Hence P<=h+27h²; no unproved monotonicity of penalty derivative is needed.
- Gauge term is zero on the straight interpolated X+ gauge. First-exit sphere of Euclidean radius4e-5 lies within original coordinatebox, including boundary. The repaired systems are covers by PLdegree; contact functions remain necessary there.
- Radial repair formula is exact. beta<.001 avoids zero chord and preserves once-winding anchor order via referencegaps>.1 and<pi/2. Interpolate all shared variables, not independently chosen hubs.
- X+ lens controls y linearly in initial anchor error, although x uncertainty is square-root. x>0 ensures arctan bound and straight gauge preservation. All anchor errors after rotation use the SAME anglealpha.
- U−r* retained, not setzero. At firstexit h<=.665[t eta+a t(1-t)beta²]; positive upper bound suffices even if actual r<r*. Negative h would itself contradict C1262. Entry ratio .84578364...<1 is exact rational inequality, not displaycomparison.
- After entry, radius<=U gives fullsite2norm<5.27e-8. At exactr* uniqueness follows, not atU.

Result: valid complete2e-6literalanchorcell handoff to localoptimality, doubled from C1324. This is still local. Existing dualslack also enters this cell; new interpolation mechanism is not a demonstrated cellsize improvement over available dualslack. Productionlabel transfer remains the existing catalogue mapping, no newmap assumed.
