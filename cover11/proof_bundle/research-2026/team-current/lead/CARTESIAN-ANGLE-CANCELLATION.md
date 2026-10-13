# Exact cancellation of hub-direction angle

C858convexlens, defineD1=2r sinb1,D2=2r sinb2; X1=v−D1cosb1,Y1=D1sinb1−t; X2=v−D2cosb2,Y2=D2sinb2+t. Lj=sqrt(Xj²+Yj²). Foractualpositiveangles A=b1−delta,B=b2+delta andfaceconstraints:
 Y1>0,Y2>0.
Proofwhen delta≥0,use H≤2r sin(b1+A) andsin delta≥0, thenH sindelta≤2r(sin²b1−sin²A); whendelta<0,Y1>0 immediate (the strongerlowerboundmaynotfollow). SymmetricY2proof when delta≤0, otherwiseY2>0 immediate. Onlypositivityneeded.

Settheta1=atan2(Y1,X1),theta2=atan2(Y2,X2),eachin(0,pi). Hubangles satisfy phi1=theta1+delta,phi2=theta2−delta (rotationidentity; actualphi in(0,pi), signexcludes2piwrap). Frozena1=z1−z9,a2=z3−z9. Thusexactcancellation:
 (z3−z1)delta+a1phi1+a2phi2=a1theta1+a2theta2.
MoreoverHarea1/2+Harea2/2=r(sin²b1+sin²b2)v+r(sinb2cosb2−sinb1cosb1)t.

ThereforeentireCartesianhubfactor equals
 lineararea(v,t)+a1atan2(Y1,X1)+a2atan2(Y2,X2)
 −z16 L1²/(4R0²)−z78 L1/(2R0)+z20 L2²/(4R0²)+z82 L2/(2R0).
NOdelta atan2,NOH sqrt, NOquadraticH²argument angle. UnfilteredanalyticextensioncanuseupperhalfplaneYj>0guard; necessarysubsetnaturalboundsmayclipYj≥0 first.

AngleswhenY=0 correspondclosuredegeneracies; continuity/atan2domainhandlingneeded, notassumedsmoothacrossorigin.
