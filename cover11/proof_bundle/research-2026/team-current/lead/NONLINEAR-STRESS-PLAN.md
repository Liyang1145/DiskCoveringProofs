# Constraint-aware max-branch stress: exact sufficient inequality

C839 angle-only model has20radius branch log functionsg_f=loggamma_f+log(q0/ell0); logRshape=max_f g_f. Let C contain the2cycle and6circle equality residuals (linear angle sums imposed directly). Candidate active setA has18branches numerically, other2inactive. Candidate KKT weightslambda_f>0,sumlambda1 and multipliermu (currently NUMERIC only).

For any fixed positive lambda summing1 and temperaturet>0 define
 S_t(a)=t log(sum_{f inA} lambda_f exp(g_f(a)/t)).
For ALL shapes, S_t<=max_{all20}g_f, by weighted exponential mean<=largest term. At a point where activeg_f agree, equality holds; gradient=weightedgradient, Hessian=weightedHessian+(1/t)weightedgradient covariance.

For rho>=0 define F=S_t+mu·C+rho||C||². On exact feasible shapes C=0, F<=logRshape. Thus proving F>=logrstar on legal angular domain implies the global covering bound. No claim that residual term itself lower-bounds infeasible covers; off equality domainF is artificial supporting function. Bound must be global and include every positive shape; C837 then handles infimum degeneracies.

At tied candidate, the augmented Hessian adds2rho J_C^T J_C and(1/t)gradient covariance to old stress. These terms are positive semidefinite and address different missing directions: compatibility violations and branch imbalance. Only common kernel J_C v=0 and (gradg_f−gradg_h)v=0 is untouched (numerically dimension4, previous positive tangent Hessian). Elementary finite-dimensional lemma: if old Hessian positive definite on common kernel, then sufficiently large nonnegative coefficients make full Hessian positive definite (compact unit sphere / Schur complement proof). This is a LOCAL existence statement at exact KKT candidate, conditional on exact positivity, not a global theorem.

Bounded next diagnostic: reconstruct full mixed Hessian, determine parameters t,rho giving numeric positive definiteness on29dim linear-angle domain, then legal trust-region samples at radius.01/.05/.2. Do not infer neighborhood remainder bounds from point Hessian or sample positivity; use results only to decide whether rigorous local/nonlocal inequality work is promising. No new broad grid expansion.
