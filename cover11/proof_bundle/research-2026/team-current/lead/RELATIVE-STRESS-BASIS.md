# Basis change for directional stress: exact transport

C919 lemma uses only BN=0 (including normalization), G=T8 N, and certified norms of N, anchor flux A, G and H0+2tau0 GG^T. For ANY fixed real4x4 R, replace N by N'=NR, G by G'=GR, A by A'=AR. Identities remain exact. Neither R positive definite nor invertible nor an exactly whitening identity is required. New stress alpha0+tau N'(G')^T x is normalized; its quadratic gain is tau||(G')^T x||². The entire ANISOTROPIC-STRESS-REMAINDER proof applies verbatim.

The numerical relative-metric design R approximately=(N^T diag(alpha^-2)N)^(-1/2) is ONLY a proposal. Certificate reads the JSON floats as exact dyadic constants, emits their floathex; no numeric spectral property of R is used. Reproducibility is pinned by basis_R_floathex in relative_stress_ball_certificate.json.

Constants interval-certified by certify_relative_stress_ball.py:
 tau0=734,tau=1468,mu=.0018; B=.495,A=.00858,Gnorm=.015363,Ccross=.0358,d=.08.
 q<=.01458 implies tau B Gnorm q<1 and
 V²-R*² >= [.0009-.0358q-(.08/3+734*(.495*.08+.00858)^2)q²]q² > .00001 q².

First attempt mu=.00199 failed interval congruence Gershgorin despite numeric min eigenvalue .002002. This is a certification-width limit, NOT a negative-Hessian witness. Conservative mu=.0018 certifies and is used above.
Scope local rawtheta8-pinned chart at exactC891root, fixed51edgeoracle. No global conclusion.
