# Bounded single-stress experiment (Round8): why scalar KKT extension is insufficient

Decision tested: after exact C839 angle-only reduction, can one candidate supporting-stress inequality prove global optimality on a larger angle domain, with the8nonlinear equality residuals merely linear Lagrange terms? This would avoid21dim constrained optimization. Test was8bounded local trials, then legal-domain local curvature control; not a blanket claim about possible dual certificates.

At candidate,18active radius branches g_f=loggamma_f+log(q0/ell0) have nonnegative normalized KKT weightslambda; 21constraint multipliersmu chosen soΣlambda gradg+mu gradC≈0,sumlambda1. Define stressL=Σlambda g+muC. On actual feasible shapesC=0 and maxg>=L, so L>=logrstar over enlarged angular domain would be sufficient. The13linear angle constraints held exactly by nullspace;8nonlinear cycle/circle constraints relaxed.

`angle_stress_probe.py` SLSQP runs1..7 wandered OUTSIDE legal sine/width domain and mostly producedNaNs. These are implementation/domain failures, not mathematical counterexamples; runs with negative constraint margin discarded. No global infeasibility reading.

Repaired `angle_stress_curvature.py` checks legal perturbations along lowest eigenvector of29dim stress Hessian. h1e-4 and5e-5 give eigenvalue approximately−11.54004; at perturbation±.01 stress decreases≈−.0005742/−.0005798 while EVERY domain inequality margin>.1. This is numerical evidence that this ONE unaugmented scalar stress cannot hold even locally off nonlinear equality manifold. No actual feasible covering counterexample; these perturbations violate8cycle/circle equalities. No analytic impossibility theorem or claim markeddead.

Next useful obligation: retain nonlinear metric/circle compatibility rather than dropping all into linear multipliers. Possibilities certified constraint-aware branching, nonlinear residual-square penalties (zero on feasible manifold), or conditional path bounds with full boundary coupling. Do NOT blindly refine independent-angle factor grids or infer sharp theorem from local KKT curvature.

Independent geometry controls `check_angle_offcandidate.py`:10random cyclic candidate perturbations reproduce actual radius and allconstraints;10noncyclic boundaries shifted along switch bisectors obey interiormetric/cycle equations but have circle residuals.0197..0537, while canonical vector closure remains1e-12. This confirms circle ratios are real constraints in angle representation, not coordinate identities. All20cases nondegenerate andpositive. Numeric calibration only.
