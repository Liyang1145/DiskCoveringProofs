# Reoptimizing the joint dual after adding face losses

The earlier pack certificates reuse site potentials y and multipliers nu,lambda optimized BEFORE face losses were introduced. There is no reason those potentials remain close to optimal for the strengthened representation.

For a fixed edge-disjoint face pack, replace each face's three edge support terms by the supremum on [0,pi]^3 of
 U^2 sum_e sin(beta_e) - sum_e (y_u+y_v) beta_e - L_f(beta),
 L_f=U^2/2 min_e(1-cos beta_e)|sum_e beta_e-pi|.
The boundary support and unused edges stay unchanged. Summing with pi(2sum y-2nu-2lambda-1) gives the same globally valid gap upper bound for ANY rational y,nu,lambda>=0 (y unrestricted).

`pack_reopt_probe.py` uses a finite sampled LP to propose these variables. A sampled LP value IS NOT a bound on the continuum, and is never used to exclude. Reconstructed rational tangents and the existing complete cube partition certify the whole continuum independently of LP correctness or feasibility. The exact Fraction replay must consume the NEW saved row in pack-reopt-probe.json, not retrieve the old row by graph index. This is a critical interface.

Control: candidate graph with a greedy edge-disjoint pack is not excluded; `pack-reopt-candidate-control.json`. Bounded12 selected graphs produced10 negative directed-interval certificates; Fraction replay pending at time of note. No new geometric premise or sharpened loss coefficient is needed for this experiment.
