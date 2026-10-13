# Exact local elimination of H and delta for the frozen seven-factor objective

Coefficient object joint_nested_frozen.json SHA2565671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb, coefficients exact9decimal; allz50..z72zero. NecessaryrelaxationC849, notglobalcoversufficiency.

## Certifiedbox andderivatives
BoxQ: r∈[.379,.38],b1∈[1.105,1.108],b2∈[1.068,1.071],delta∈[.035,.040]. A=b1−delta,B=b2+delta. Intervalcertify_h_monotone_box.py enclosesentireprojectedHfiber [.3034806266617412,.6271676523896763]. Splittingthisfiberinto64closedsubintervals andintervalevaluatinganalyticFH' givesFH'>=.324122527140786>0. Formula inH-STATIONARY-POLYNOMIAL.md, differentiatingdirectsqrt/atan2; allQj strictlypositive.
Hubnormupper boundis>=1.5425278991, bothfaceupperbounds<=.6275965948, soHmax=min(h1,h2),h1=2r sin(2b1−delta),h2=2r sin(2b2+delta). No otherHupperconstraint omittedfromC848. IfactualHfiberempty, thatoutertuple isirrelevant; otherwise maximizingH putsitonthisupperendpoint.

OnQ bothsineargumentsarein(π/2,π). Thereforeh1<h2 iffdelta<b1−b2: h1 increasesindelta,h2decreases. Atfixedr,b1,b2,widths, totaldeltadependenceis(z3−z1)delta+FH(delta,H). certify_delta_ridge.py differentiates thisafterH=h1 andH=h2 withoutclipping; intervalresults
 leftbranchderivative∈[.09428709877,.23048129810],
 rightbranchderivative∈[−.22693326512,−.09032456306].
TheseholdthroughoutQ independentlyofwidths. Analyticcontinuationremainswell-definedevenif someprojectedH violateshubnorm, so nofeasibilityholespreventcomparisonalongdelta.

## Exactlocalmaximumreduction
RestrictQtoQ0 withb1∈[1.106,1.108] (otherboundsunchanged). Thenridge delta*=b1−b2 belongs[.035,.040]forallr,b1,b2. Onridge H*=2r sin(b1+b2) satisfiesbothfaceupperconstraintsexactly. Intervalchecks in delta_ridge_feasibility.json: H*−2r|sindelta*|>=.5916803260>0, H*²−2s cosdelta*H*+2r(1−r)<=−.2862141642<0. PositiveA=b2,B=b1. ThusridgealwayshasnonemptyC848Hfiber. WidthfibersC849 independentofdelta/H.
Consequentlyforallfixedr,b1,b2 inQ0 andeveryadmissiblewidthpair, the maximum ofthefrozenobjective overactualC849(delta,H)fiberwithdelta∈[.035,.040] occursat(delta*,H*). ThiseliminatesTWOvariablesexactly ONTHISBOXONLY. It doesnotassertactualglobalcovercanbemovedtherewithoutchangingoutsidefactors; resultconcernsthelocalrelaxedobjective usedforupperbounding.

## Radicalfree ridgeform
Let t=r/R0. Onridge A=b2,B=b1, H*=2r sin(b1+b2). Thefirstfaceoppositeedge lengthL1=2r sinb2, secondL2=2r sinb1; hubanglesphi1=b1,phi2=b2. This follows eithertrianglelawofsinesor H*−2r sinb1 cosb2=2r cosb1 sinb2, andsymmetricidentity.
Hence FH*=4r² sin(b1+b2)sinb1sinb2+(z1−z9)b1+(z3−z9)b2−z16 t²sin²b2−z78 t sinb2+z20 t²sin²b1+z82 t sinb1.
Combininglinear(z3−z1)delta* exchangesb1/b2coefficients: (z3−z9)b1+(z1−z9)b2. No square roots oratan2 remaininthehubpart. Widthtermsstaythesmoothcancelledepression ofSMOOTH-PATCH-CANCELLATION.md.

Localnewrepresentation:3outerparameters(r,b1,b2)+2independentwidthfibers ratherthan4outer+3fibers. Exteriorparameterdomainstilluncontrolled; globalsharpinequalitynotproved.
