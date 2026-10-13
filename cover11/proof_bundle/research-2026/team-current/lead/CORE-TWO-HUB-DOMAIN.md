# Exact core-covering reduction for two hub positions

D unit disk, r<=19/50, a=1-2r>0. Nine ring disks cannot cover any point of open B(0,a), so two hub disks of radius r must cover closed B(0,a). Write s_j=|h_j|. This note gives necessary geometric constraints; it does not assert sufficiency for covering the full hole.

Branch A: if some s_j<=r-a=3r-1 (necessarily r>=1/3), that hub alone covers the core. The second hub is constrained only by other obligations. When r<1/3, branch A is empty.

Branch B: neither hub alone covers the core. Each must intersect the core boundary in a positive-length proper arc; otherwise the other proper arc cannot cover the entire circle. Its angular half-width is

  b_j = acos((a²+s_j²-r²)/(2as_j)),   0<b_j<pi.

Let delta in [0,pi] be the smaller angle between nonzero vectors h1,h2. Two proper arcs with respective center angles and halfwidths cover the entire core circle iff

  b1+b2 >= 2pi-delta.

Indeed the shorter gap delta and longer gap 2pi-delta between centers must both be spanned by the sum of halfwidths; the longer is binding. This implies b1+b2>=pi. Since acos(u)+acos(v)>=pi iff u+v<=0, this gives

  (s1+s2)*(1-(r²-a²)/(s1*s2))<=0,
  hence s1*s2 <= r²-a².

Therefore, assuming r>a, after swapping labels at least one hub satisfies s1<=sqrt(r²-a²). In Branch A the same bound holds because 0<=r-a<=sqrt(r²-a²). At r=19/50 this is sqrt(217)/50≈.294618; this display is numeric, the radical exact. Both hubs also satisfy s_j<1-r by the global strict-interior reduction.

This position-domain restriction is valid for covers, not for arbitrary legal ring ledgers. It is a necessary filter for a future three-circle dual: S(0,1) covered by rings, each S(h_j,r) covered by rings plus the other hub (outward-limit argument or radial Voronoi-facet identity). Rotation can set h1=(s1,0), leaving s2 and delta. No certificate on this 3D domain is asserted here.

Degenerate caveats: s_j=0 belongs to Branch A only if r>=a; otherwise that hub covers no core-circle point and the other must alone cover it, impossible for r<a. If r<a, neither radius-r disk can cover half a core circle, so two cannot cover it, which gives r>=1/3 as a simple necessary bound. At r=a, antipodal semicircle coverage would require s_j=0 in the limiting inequality, but this note does not need an equality classification.
