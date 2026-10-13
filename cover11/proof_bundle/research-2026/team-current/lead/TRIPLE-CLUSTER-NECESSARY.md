# Triple-ring common-point subclass: exact necessary localization

Object: nine radius-r disks cover the unit circle, 0<r<=19/50. Suppose three designated disks share a point p. The following statements do not assume zero arc overlap, symmetric centers, or that hubs exist. Their use in the unrestricted 9+2 problem remains conditional on the existence of such a triple.

Let a=asin(r), b=asin(2r). The three-disk union is contained in B(p,2r), whose covered boundary arc has half-length at most b.

1. Each of the remaining six disks has actual boundary half-width

   t_j >= t0 := pi-b-5a.

Indeed removing that disk leaves at most half-measure b+5a; all nine cover half-measure pi. Here t0>0 for r<=.38, since b<.9 and a<.4 gives t0>pi-2.9>0.

2. Each of those six disk-center radii is at least

   rho0 = cos(t0)-sqrt(r^2-sin(t0)^2)

whenever the hypothesized triple subclass is nonempty. For otherwise t0>asin(r) immediately contradicts the feasible half-width bound. The inward root rho_-(t) is increasing on [0,asin(r)] and the outward root is at least the inward root, so the conclusion applies even before inward-root replacement. Thus their disks avoid the open core B(0,rho0-r) when rho0>r. This is a core unserved by these six disks only, not a hole in the full nine-ring union.

3. Put T=pi-6a. The disk B(p,2r) must cover boundary half-measure at least T. If T>asin(2r), the whole triple subclass is excluded. Otherwise, with d=|p|,

   (d-cos T)^2 <= 4r^2-sin(T)^2,

hence cos T-sqrt(4r^2-sin(T)^2) <= d <= cos T+sqrt(4r^2-sin(T)^2). This follows from the exact boundary-arc formula cos(halfwidth)=(1+d^2-4r^2)/(2d); d=0 is impossible since 2r<1. The domain T>0 is automatic at r<=.38.

At r=.38, noncertified display-only readings: t0≈.3292980562, rho0≈.7467047942, rho0-r≈.3667047942; T≈.8028148747; d∈[.4493546809,.9400146878]. Analytic statements above, not these rounded endpoints, are the evidence. The simpler triple capacity contradiction holds when 6asin(r)+asin(2r)<pi (numeric crossover .373645528, not certified here).

Next missing implication: prove that three disks with this common point, together with only two interior disks, cannot cover the remaining region while the other six retain the required large arcs. This is not established. The localization is intended to reduce that subproblem rather than certify it by sampling.
