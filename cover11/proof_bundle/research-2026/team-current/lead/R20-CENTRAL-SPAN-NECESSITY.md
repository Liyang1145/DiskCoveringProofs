# Central two-triangle span bound (necessary, not sharp)

Fixed unit-disk cover radius r in q0(6,7). Let hA,hB be distinct hubs, d=|hA-hB|, m midpoint, and shared ring endpoints c0,c4 on opposite sides of the hub edge. Suppose both central triangles have positive area and circumradius<=r. Then d<=2r and k=sqrt(r²-d²/4). Choose unit normal n toward c0.

The circumradius product identity (R20-CHAIN-HUB-CONVEXIFICATION.md Lemma2, now base=hA,hB) says c0 belongs to the closed disk B(m+kn,r) and c4 to B(m-kn,r). For a point on +n side the first distance is smaller; product<=0 therefore requires it<=r, with the other>=r. The opposite holds for c4. Consequently
 D=|c0-c4| <= 2r+2k.
If D>=2r this gives d²<=4rD-D². If D<2r, only d<=2r follows; do not square D-2r with incorrect sign.

Combined with C879 convex chain hub regions KA,KB, a necessary condition is
 dist(KA,KB)² <= 4rD-D² (when D>=2r),
where distance is between actual strict-hub regions or their closed relaxations (the latter gives a weaker necessary condition). The argument does NOT fix center orientation or saturate individual triangle radii. It only removes configurations when the two convex sets are separated too far relative to endpoint span. Converse false; triangle orientation and two precise crescents remain. At saved candidate the inequality has visible slack, so it cannot alone be the sharp certificate.

This bound is elementary triangle inequality, not claimed novel. The potentially useful new interface is combination with exact chain hub convex sets, enabling deterministic convex-distance certificates over fixed/moving ring boxes. Global ring domain still unresolved.
