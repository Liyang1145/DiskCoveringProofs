# High-bearing hub-norm-saturated sector2 exclusion

## Certified sevenfactor bound
For everylegalC848/C849 necessarypatch with r∈[3/8,19/50], b1,b2∈[1,acosr], and |c9|=1-r, thecurrentfrozen sevenfactor objective J <=28.103152 (conservative rounding of28.103151732510887939...). Bothnormcirclepolarroots are included, includingzero discriminant, and everydelta in[-b2,b1]. No claim aboutinteriorhubpoints orface-onlyboundary points.

Evidence patch_outer_norm_boundary_certificate.json:51outerevaluations,0liveboxes,no budgetexit. Cover broadouter[rlo,.38]×[1,acos(.375)]², rlo=nextfloatbelow.375. Codecertify_patch_norm_boundary.py retainsallterminaluppers; target28.105 isonlysearchterminationthreshold. Everydiscard usesnecessaryinfeasibilityfilter; noabsence inference fromsampling.

## Critical kernel interfaces
- interval_hub_saturated.py branches2/3 areexactnormquadraticroots H=s cosdelta±sqrt((1-r)²-s²sin²delta), bothretained; clippedpositiveHlower s-(1-r) isnecessary triangleinequality. H<=2r andtwofacecaps necessary. No unsaturatedfaceidentityappliedtothese branches (j=2/3 differsfromfacei=0/1).
- Widthdomains fromC850 andscalarobjectivefromC852/C849. base.setup usesfullvinterval[.3,.76], validforalllegalr[.375,.38] becausev>=s-(1-r)>.3. Broadtintervalproducesa supersetoflegaldelta/H andcannotdiscard alegalwidth/hub. Underhighbearingstrictlypositiveedge lengththeanglebranchiscovered; uncertainzero/radicand intervalsretained, nottreatedasexactzeros.
- sqrt/lengthclipsandarcconstraints applyonlynecessaryphysicalinequalities; noTaylorboundcrossingbranches. ExistingwidthMVTguardsareinheritedunchangedfromC854andfullanalyticderivativeWIDTH-BEARING-PARTIAL.md.
- Sourcehashesandcurrentz digest stored. Sevenfactorpartition identicaltoC859.

## Different-coordinate control
norm_cartesian_control_certificate.json parameterizes the SAMEfullnormcircle directlyby(v,t)=(s,0)+(1-r)(cosθ,sinθ), θ∈[-pi,pi], usesCartesiananglecancellation andlineararea ratherthanpolarquadraticroots.45outerevaluations,0liveboxes,no budgetexit; upper28.104759566903198<28.105. Thisindependentlychecksdomain/branch/objectivegeometry, although bothcontrols reusewidthandintervalinfrastructure. Itdoesnotmakeasharedhelperindependent.

## Actualcover exclusion
Restricttoactualinwardq0flatsector2coversat r∈[.379,.37999] and b1,b2>=1, withhubnormsaturated. The22complementboundsfromC859 coverthisscope. assemble_norm_boundary.py exactcurrentz+outwardbinary22uppers gives:
 const+sum22=-24.96545276218283632963030154323316287029...,
 polarassembly<=3.137698970328051610<pi,
 Cartesiancontrolassembly<=3.139306804720361436<pi.
Thus SUCHactualcovers impossible. Same7+22disjointpartitionandconstantasC859; current22_manifest.json pins22files. This doesnotexcludeallhighbearingcovers: arbitraryhubcouldmaximizeontwofacearcs instead(C861), and after C861 thepotentialnorm-boundarymax isbelowtarget butfaceboundarymaxremainsto bound. C862asymmetriclargerregionnotcoveredbythiscertification.

Nextobligation: bound thetwofacearcs (includingcircleintersections) onhighbearingdomain; separatelyhandlelowdistancebranchwhichhasnumericalpeak28.10424 close totarget28.107045.
