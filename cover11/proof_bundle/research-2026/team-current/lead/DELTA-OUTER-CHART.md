# Recenter outer sharedhub angle

C848 delta=b1−A, B=b2+delta, A=b1−delta. Inactualpositivefacebranch delta∈(−b2,b1)⊂(−pi/2,pi/2). Hubnormdiscriminant D=(1−r²)cos²delta−2r(1−r)>=0 implies
 cos²delta>=2r/(1+r),
 **|delta|<=acos sqrt(2r/(1+r))<=acos sqrt(6/11)** forr>=3/8.
ReplacingouterA∈[0,2acos(3/8)] bydeltaintheaboveuniforminterval is exactlinearcoordinatechange plusnecessaryprojection; no symmetryassumption. interval_patch_delta.py retainsr,b1,b2,delta, computesA/Bbyintervalintersection[0,pi], usesdelta directlyforhubnormfiber, preservingcenteranglecorrelationotherwise lostinb1−A. ActualpositiveA/B interior notdiscarded. Widthfibers unchanged. Numericalpointcontrol validatesinterface; fullbounded4Dcoveragejobcertify_patch_delta.py appliesallC849necessarybounds.
