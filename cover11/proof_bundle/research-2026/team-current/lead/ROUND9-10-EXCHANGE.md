# Rounds 9–10: continuous separation and a conditional certificate attempt

The original goal remains sharp, unconditional n=11 optimality. No sharp conclusion yet. Current obligation: eliminate the middle ring sector 2 flattening branch, in the remaining q0(6,7) topology. This would remove a configuration boundary but would not prove optimality.

## Continuous separation repair
The previous finite grid proposal was invalid as a continuum bound. A bounded exchange now constructs off-grid atoms, using full local objective values, and appends them to the finite LP. Face and switch local radii are optimized by the exact quadratic formula evaluated numerically; rings obey C844's inward norm constraint. Sector 2 is replaced by its entire degenerate segment alpha=pi, u=v=t in [75/76,1].

Five initial exchange rounds reduced the numerical aggregate from 3.16186358164 to 3.14515796807, still above pi. Ten additional rounds used the existing off-grid planes rather than refining grids. Rounds 10–14 all produced numerical aggregates below pi; the last was 3.14123003341214. This is only numerical: constrained optimizers can miss maxima. Scripts and every atom are retained in exchange_middle_inward_dual.py, exchange_middle_inward_refine.py and their JSON histories.

The best coefficients were rounded to exact nine-place decimals and frozen in middle_inward_frozen.json. Do not overwrite this file or reuse bounds for another coefficient vector. SHA256: 17a0225e7fc329b54c78e5dab04b7f1dff30c61c721f81659d6c92aee4ad139d.

## Interval attempt
certify_middle_inward.py uses the previously audited full-domain interval kernel, with an additional C844 infeasibility filter on every ring factor. A box is discarded only if its maximum possible inward-norm LHS is strictly less than its minimum RHS. The objective is still enclosed over the whole box; partially feasible boxes are never contracted without a new enclosure. The conditional ring2 factor uses the whole t segment. All other 28 factors are recomputed with the frozen coefficients.

The runner stores the maximum of live and discarded upper bounds, so even a budget-limited factor yields a sound (possibly useless) upper bound. Each factor has 200000 evaluations maximum. Initial target tolerances are 5e-6 for faces/switches/corner and 15e-6 for other rings; tolerances do not replace computed upper bounds. Every output is a separate file bearing the coefficient hash. All 20 face/switch factors have finished. Ring factors are still running as of this note. No new impossibility claim is registered until all factors assemble below pi.

Exact coefficient cancellation audit: check_middle_sector_symbolic.py, middle_sector_symbolic_control.json. This is independent formal Fraction accounting, not a second interval kernel. Two members are working on (i) interval-filter interfaces and (ii) an exact scale-fiber elimination. Do not treat member identity as independent mathematical evidence.

## Final audit outcome: candidate rejected, representation improved
The interval attempt exposed a genuine omission in the continuous separation oracle: narrow alpha≈0.049404 branches were missed. Factor ring1 has attained value about 1.44594555, versus the oracle's 1.38490294; ring3 similarly 1.46110153 versus 1.40232187. These are not rounding effects. A debug point in middle_inward_debug_21.json has strictly positive inward margin 1.20e-7 and a directed objective lower bound 1.445940961. Consequently the numerical preview below pi is not a continuum bound. The full certification job was stopped after factors0..25 completed. Factor26 partial was not saved. No conditional exclusion was proved.

A member audit falsely attributed the failure to factor22: it compared an unrestricted sector against the explicitly conditioned alpha2=pi slice, and used inconsistent coefficient indices. C845 was retracted. Correct corner endpoints at t=75/76 and 1 are both approximately -2.70892563924, inside the stored interval upper. Member derivative counterexample was also incorrect: uv sin(alpha)/sqrt(q)<=min(u,v)<=1 proves the clip. Invalid report archived; no earlier certificate affected.

Lead derived and proved C846, an explicit omega=w/2 scale fiber (SECTOR-SCALE-FIBER.md). Calibration checks 20000 off-candidate equivalences and the exact trig identity, but the proof is analytic. The first full-range fiber DE still missed narrow branches; partitioning alpha search exposed them. These partitions are only diagnostic, not a claimed global optimizer. Another five exchange rounds with these atoms gave finite LP objectives rising to 3.14541753692 and best numerical aggregate3.14597772466>pi. With this coefficient box and relaxation there is no current exclusion proposal. Do not scale the same search. Either strengthen inter-factor constraints or exploit the exact metric model.

Additional exact elementary endpoint bound: u,v>19/100, hence |d|<log(100/19)/2; proof INWARD-ENDPOINT-SEPARATION.md. This bound concerns boundary endpoint distances only, not all site distances/radii.
