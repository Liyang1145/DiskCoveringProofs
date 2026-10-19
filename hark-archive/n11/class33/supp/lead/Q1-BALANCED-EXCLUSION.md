# Balanced q1 exclusion: certificate work log

Object: nine essential ring sites, two indispensable hubs, inward-root replacement, refined nearest-cell graph q1 and hub degrees(6,6), R=19/50. No symmetry hypothesis or arc-overlap restriction.

Graph scope: ear(0,1,2), core[0,2,3,4,5,6,7,8]. A balanced hub spans four edges of this8-cycle. Starts0..7 partition under label reflection and hub exchange into{0,1,4,5} and{2,3,6,7}; representatives0,2. `check_shared_moment_dense_symbolic.py` checks both orbits and the exact multiplier identity.

Area bound: use C817's exact face/switch/sector decomposition and additionally enforce first powers of every shared side and switch radius alongside their squares. This is valid for all genuine geometries; no moment-realizability premise is assumed. The extra multipliers improve only the decoupled relaxation. Face/switch radius maximization reduces exactly to a scalar quadratic support Q; proof and formulas in SHARED-MOMENT-DUAL.md. Ring terms are still global3D suprema. All closed domains, including zero-radius/angle limits, are enclosed.

Certificate generator `certify_shared_moments_dense.py`: rational9-place coefficients from `shared_moment_dense_{0,2}_4.json`, graph reconstructed independently, interval subdivision of29 factors, all pruned boxes retained by their upper bounds. New face bound intersects natural intervals with envelope-gradient intervals: maximizing radii bracketed by quadratic coefficients' corner maximizers. Monotonicity follows from increasing differences in radius and each coefficient. At ties retain the full possible maximizer range. For boxes crossing the triangular face boundary use only direct intervals.

Controls: `check_quadratic_support.py` compares3000 rational coefficient boxes against independent Fraction exact endpoint/vertex formula; this is instrument calibration, the analytic monotonicity proof is the universal argument. `check_shared_moment_dense_symbolic.py` uses independent formal atoms to check exact rational coefficient cancellation; `check_shared_moment_identity.py` evaluates the dual on two saved metric-compatible states, residual<3e-12 (numerical calibration only). Prior coordinate-area controls still apply unchanged.

Initial coarse-grid proposal was NOT enough: continuous start2 bound3.164374>pi. Denser proposal uses switch domain matching the certificate and radius grid24; initial interval tolerance.00012 gave start0<3.137389 but start2≈3.141897. Tightening interval tolerance to.00004 on the SAME coefficient sets is in progress; no new mathematical premise or numerical optimality assertion introduced.

Final results must be recorded from output files after both complete successfully, before registering an exclusion claim. Remaining original goal even after q1 exclusion: q0 degrees(4,9),(5,8),(6,7) and sharp optimum bound; no goal completion follows.

## Final certified result (round3)

Both completed at tolerance0.00004, with no change to exact coefficients:
- start0: [3.13549360291499034831398630214,3.13549360291499034831398671573] <3.135494<pi;
- start2: [3.13981254422259203355720467746,3.13981254422259203355720550464] <3.139813<pi.

Thus all balanced q1 graphs are impossible at r<=19/50. Combining C809, C812, C813, C817 excludes ALL q1. Every remaining globally reduced eleven-disk cover at this radius has q=0, i.e. no refined ring-only ear, and refined hub degree pair(4,9),(5,8),or(6,7). This does not yet prove the sharp optimum.

Evidence: shared_moment_dense_certificate_0_4.json; shared_moment_dense_certificate_2_4.json; moment_dense_certificates.log (empty .err). Reproduce `py -3 -B research-2026/team-current/lead/run_moment_dense_certificates.py`; controls `check_shared_moment_dense_symbolic.py`, `check_shared_moment_identity.py`, `check_quadratic_support.py`. No independent second full arithmetic kernel is claimed.
