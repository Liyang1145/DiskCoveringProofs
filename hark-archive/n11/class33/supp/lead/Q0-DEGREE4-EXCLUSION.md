# q0 degree(4,9) exclusion at R=19/50

Object: established globally reduced unit-disk eleven-disk cover,9 essential ring sites2 hubs, inward-root representation, q=0 refined nearest-site triangulation. No ear-only capacity hypothesis is used.

With no ears the graph consists of two fans on the ring9-cycle and two triangles containing the hub-hub edge. Up to ring relabeling and hub swap, the smaller fan spans k=2,3,4 edges, giving hub degrees(k+2,11−k). Faces: (9,i,i+1),0<=i<k; (10,i,(i+1)mod9),k<=i<9; (9,10,0),(9,10,k). Thus degree(4,9) is the single k=2 graph. Always11 faces21 edges. Saved certified upper candidate's coordinate Delaunay graph has no ears, hub degrees(7,6), consistent with k=4 (coordinate calculation is calibration, not an exclusion premise).

Use C818 first+second shared-side/radius factor dual on this graph. The old ear-capacity multiplier eta is EXACTLY ZERO; verifier asserts this. Hence no outside-six width inequality enters the conclusion. All other area and matching identities are unchanged.

Directed continuous certificate:
 A <= [2.97871288362012352436665185421,2.9787128836201235243666522678] <2.978713<pi.
Thus q0 degree(4,9) impossible for r<=19/50. Together with C818, only q0(5,8),(6,7) remain globally.

Evidence: q0_moment_certificate_0_2.json; certify_q0_moments.py; certify_q0_moments.log (empty .err). Exact symbolic control `check_q0_moment_symbolic.py` checks all three q0 graph coefficient identities using formal first/second side/radius atoms. Quadratic-support and interval/envelope controls from C818 remain applicable without changes. The q0 verifier independently reconstructs its graph and asserts zero eta. Full boundary/degenerate factor domains retained.

Repro:
 py -3 -B research-2026/team-current/lead/certify_q0_moments.py 0 2
 py -3 -B research-2026/team-current/lead/check_q0_moment_symbolic.py

Remaining gap: sampled first+second moment duals atR=.38 give roughly3.16297(k=3) and3.28170(k=4), neither a certificate nor a real geometry. Need additional coupling/realization conditions, especially for the sharp k=4 candidate. Original global optimum remains unproved.
