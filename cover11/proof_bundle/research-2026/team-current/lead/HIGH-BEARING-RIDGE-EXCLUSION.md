# High-bearing ridge exclusion (restricted q0 flat patch)

C867 supplies exact separation of the frozen seven-factor ridge objective using tangent tau=87/40 to the concave function -sin(2T), T=b1+b2. No endpoint domination assumption is made.

Scope: actual unit-target-disk radius r in [.379,.37999], b1,b2 in [1,acos r], delta=b1-b2 and H=2r sin(b1+b2), legal width fibers of C849. Frozen z SHA256 5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb.

certify_ridge_tangent.py covers an outward-rounded product box containing all legal radii, bearings and widths. Component bounds use full-extension analytic AD/MVT, not clipping physical constraints inside derivatives. Reverse triangle guards on q and denominator are valid analytic inequalities over the full box. Necessary-only filters cos(b)>=r and q<=r² reject only boxes entirely outside their respective constraints. Binary splits retain both endpoints. All terminal upper bounds are retained; both queues are empty after817/831 evaluations.

Component uppers: -0.047820961396975545 and -0.04684231595647687. Constant interval upper: 28.2015638724124935775194169428. Outward-assembled seven-factor upper: 28.1069005950590415920942177763208746910095215.

Matching remaining22 factors and dual constant yield total <3.141447832876205263<pi, strict gap >.00014482071358797. Hence a feasible actual flat q0 patch cannot lie in this high-bearing ridge subset, conditional on the frozen necessary dual relaxation and complement certificates. This is NOT full high-bearing patch exclusion or global n11 optimum.

Evidence/repro: ridge_tangent_certificate.json (source and coefficient hashes), ridge_tangent_assembly.json; py -3 -B research-2026/team-current/lead/certify_ridge_tangent.py; py -3 -B research-2026/team-current/lead/assemble_ridge_tangent.py. Independent source audit R17-C867-RIDGE-AUDIT.md; ignore its numerical-grid language for concavity (the exact interval inclusion pi<2T<2pi proves it analytically) and its suggestion an optimizer must sit near tau (not implied). Audit's failed auxiliary probe scripts are not evidence. Principal full-expression controls are check_ridge_split.py with exact trig algebra and 30 point interval comparisons.
