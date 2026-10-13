# Angle-only exact model: eliminate ALL20 local radius variables

Scope: C838 positive model, retaining11site triangle sums,2hub sums, sector positivity and widths0<w<pi.42angles=(33site-face angles,9switch half-angles). All site angles in(0,pi), switch halfangles in(0,pi/2) on existing inward positive graph branch (allowpi/2 only as infimum limit if needed).

## Connected factor adjacency and two cycles
Nodes are11site-face factors and9switch factors.21site-side matching equations link the two factors sharing a site-site edge. This graph is connected: dual adjacency of triangulated site disk is connected, switches are9leaves attached along boundary edges. E−V+1=21−20+1=2. Choose a spanning tree, rootface0, base local radiusgamma0=1. For oriented edge(f,g), let a_fg be angle opposite shared side in facef (site-face angle, or switch half-angle for a switch). Sine-law matching:
 gamma_f sin(a_fg)=gamma_g sin(a_gf).
Thus recursively gamma_g=gamma_f sin(a_fg)/sin(a_gf)>0. This defines all20positive gamma fromangles alone; the2non-tree edges give EXACTLY2remaining sine-product cycle equations. No coordinate-closure identity may replace those unless full realization is already assumed.

All feasible intrinsic local radius vectors are y_f=t gamma_f for some t>0. Constraints y_f<=1 are equivalent t<=1/M whereM=max_f gamma_f. Sector chord from switch endpoint radii has length t ell_i(gamma,alpha); all boundary turns and widths depend only onangles andgamma ratios, nott. Define q_i=2sin(w_i/2). Six circle-ratio constraints are scale-free q_i/ell_i=q_0/ell_0 fori1..6; remaining2followC838.

The covering allowance is R=q0/(t ell0). At fixedangles it is minimized by largestt=1/M. Therefore
 **R_shape(angles)=M q0/ell0**, M=max_{20}gamma_f.
This eliminates all20radius variables ANDR EXACTLY, without choosing which factor attainsM and without setting others to1. Root choice rescalesgamma andell together, so objective and constraints root-invariant.

Remaining domain:42angles;13linear equalities (11triangle sums+2hub sums),2nonlinear sine cycle equations,6circle consistency equations =21degrees generically. Sectoralpha derived from ring sums must lie(0,pi); recoveredw0..8 in(0,pi); Rshape<.38 (for the relevant global infimum). The graph metric gluing guarantees realization by C835. Global infimum transfer C837 applies. Actual switches b=pi/2 cannot occur for distinct sites strictly inside boundary unitcircle with switch atPi outside site convex hull: Pi is not midpoint, so b<pi/2 on inward geometry. Positive sufficiency on this chosen domain remains valid.

This is genuine parameter elimination, not lower-dimensional symmetry: all positive realizable metrics represented up to irrelevant uniform scaling. The remaining21shape variables still require global analysis. Singular limits may blow individualgamma in this root gauge; objective root-invariant and compactification/interval coordinates must handle that, not impose arbitrary log cutoff.
