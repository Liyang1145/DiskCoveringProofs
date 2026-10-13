# Exact saturated-face chart after C861/C862

On the firstfacecircle, polarhubcoordinates obey H=2r sin(b1+A), A=b1-delta (H>0). For the triangle(c2,c1,hub), its otheredgeL1=2r sinA and angleat hubphi1=b1 exactly. Proof in localpolar coordinates:
 X=H-2r sinb1 cosA=2r cosb1 sinA,
 Y=2r sinb1 sinA,
 so atan2(Y,X)=b1 since sinA>0 andb1∈(0,pi/2). Bothsquarededge andanglecollapse; no intervaltestforzero/rank.
Analogously onsecondfacecircle H=2r sin(b2+B), B=b2+delta, L2=2r sinB,phi2=b2.

Fullhubobjective inpolarform includes (z3-z1)delta andfaceangularcoefficientsa1=z1-z9,a2=z3-z9. The area is H*r*(sinb1 sinA+sinb2 sinB). Onboundary1 usea1*b1 andquad(beta1,gamma1,L1/(2R0)); onlysecondface needsatan2/sqrt. Onboundary2 viceversa. Thewidthfibers areindependentofdelta (C852cancellation), so this is3outerparameters andoneboundarydelta scalar.

Boundarynormdisk: H²-2s cosdelta H+2r(1-r)=0 gives H=s cosdelta±sqrt((1-r)²-s²sin²delta). Bothbranchesmustberetained; radicand>=0, H>0, twofacecaps required. Thefacecirclescontainorigin, but originnotfeasiblebecausehubnormforcesH>=s-(1-r)>0. Everyboundarypoint iscoveredbyoneof2facebranches or2normbranches. δ∈[-b2,b1] coverswedgeclosure; exactwedgeendpointsinfeasiblebyC861/C862proof. NonuniformparameterboxesneednecessaryA,B,H filters, neverdropuncertainbranches.

This is a representation identity and boundarycover, notproofthatonebranchdominates. Intersections maybeduplicate harmlessly. Applicability of boundary-onlymaxrequiresC861orC862; withoutitthese4branchesarenotexhaustiveofinteriorhubpoints.
