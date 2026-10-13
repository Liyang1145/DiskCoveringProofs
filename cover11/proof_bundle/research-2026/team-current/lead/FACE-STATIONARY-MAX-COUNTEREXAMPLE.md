# Certified counterexample to 'all legal face-arc stationary points are minima'

Frozen C849 seven-factor objective; widths fixed at ANY legal values (their contribution has no delta dependence). Physical r=377/1000,b1=126/125=1.008,b2=1001/1000. Face1 saturated, H=2r sin(2b1-delta), delta in [-8/25,-31/100].

Using the Cartesian circle chart, independent second-order interval AD gives G'(-.32)>0.00155934219339664 and G'(-.31)<-0.00270987909100015. On the entire interval, split into100 exact decimal subintervals, G''<=-0.3872497301616168<0. Every subinterval is strictly inside the second face disk and norm disk, H>0, and strictly inside the wedge. Face1 membership holds identically by circle parameterization, not by an interval containing0. Bearings satisfy cosbj>r; widths exist (e.g. w=.5; original C849 width upper is larger, check if using explicit width extension).

Thus by continuity and IVT there is exactly one stationary point in (-.32,-.31), and it is a strict local maximum of the hub objective on the legal face1 arc. This disproves the proposed universal stationary-minimum criterion, the disjunction G'!=0 or G''>0, and any everywhere-strict integrating-factor inequality G''+kG'>0 on this arc. It does NOT show this local max exceeds the full arc endpoints, nor disprove endpoint domination by some other argument, nor provide a covering counterexample.

Evidence: face_second_jet.py (direct Cartesian second AD), certify_face_stationary_max.py, face_stationary_max_certificate.json. Both Cartesian and polar inequalities certify strict feasibility; formula |x-Di|²-r²=-H(cap_i-H), with Di fixed, controls interface. Original polar derivative at calibration(.375,1.05,1.05,0) agrees with independently repaired hand derivative to displayprecision; this is calibration, not the proof.

Run: py -3 -B research-2026/team-current/lead/certify_face_stationary_max.py.
