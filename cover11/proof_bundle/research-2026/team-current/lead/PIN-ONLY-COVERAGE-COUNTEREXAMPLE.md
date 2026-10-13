# Pin-only feasibility is not a disk-cover certificate (exact)

Object: closed unit target disk, common radius r=19/50. Keep nine ring centers exactly as the rational integers /10^17 in `n11/upper/certified_object.json`; replace original site2 by A=(2653,2729979)/10^7 and original site0 by B=(-1928,-1494489)/10^7. All ring centers remain canonical inward centers, and their arcs cover the unit boundary (the original certified cover uses smaller radius, with strict interior hubs). Both new hubs have norm<1−r.

Ring cyclic order is [5,7,1,8,6,4,9,10,3]. Assign pins on edges [(5,7),(7,1),(1,8),(8,6)] to A and [(6,4),(4,9),(9,10),(10,3),(3,5)] to B. A pin means the smaller-norm intersection of the two RADIUS-r ring circles, not a switch on the unit circle.

All nine assigned pin distances are STRICTLY less than r. Independently, all nine corresponding fan triangle circumradii are STRICTLY less than r. Nevertheless the rational circumcenter p of (A,site5,B) is strictly inside the unit disk and has distance STRICTLY greater than r from every one of the eleven centers. The minimum squared-distance excess is >3/10^6 (diagnostic decimal 0.0000030443627455622447). Thus the central conditions are independent necessary constraints: pin coverage is not sufficient, even for canonical boundary-covering rings arbitrarily close in numerical scale to the saved candidate (no quantified arbitrary-closeness assertion).

## Exact algebra and independent controls
For ring endpoints a,b let d=b−a,m=(a+b)/2,Jd=(-d_y,d_x),q=r²/|d|²−1/4. pin=m+s sqrt(q) Jd with s=−sign(m·Jd). Each membership residual is u+v sqrt(q), u=|h−m|²+q|d|²−r², v=−2s(h−m)·Jd. Its exact sign follows from signs(u),signs(v), and comparison u² versus v²q; five positive/negative/zero calibration cases are included. No floating-point comparisons enter this verification.

Independent fan check uses Rc²=|a−h|²|b−h|²|b−a|²/[4 det(a−h,b−h)²]. For p the two perpendicular-bisector linear equations have rational coefficients, so p and all eleven distance comparisons are rational. This direct uncovered-point check requires no Delaunay or inverse-trigonometric branch assumption.

Lead evidence/repro: `py -3 -B -X utf8 research-2026/team-current/lead/check_pin_only_counterexample.py`; exact full rational output `check_pin_only_counterexample.json`. Member independently discovered the direction, then produced `r20-geometry/exact_missed_point.py/.json`; its initial radical sign helper had an erroneous negative square, identified in lead audit and being repaired. Lead kernel does not import that helper.

Scope: disproof of sufficiency of the nine pin/fan constraints alone. NOT disproof of global optimum, C900/C904, or existence of some alternate pair of hubs covering these same rings. NOT an impossibility proof for line-based elimination. Not yet a claim that all residual-boundary vertices (rather than these nine particular pins) are covered; that stronger phrasing would need enumeration.
