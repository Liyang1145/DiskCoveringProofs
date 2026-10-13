# Polynomial interface for the compact remaining branch

Purpose: an alternative to atan2/log-sine evaluations, not another theorem asserting sharpoptimality. C835–C841 establish positive metric sufficiency and compact necessary-domain search. The original sharp implication is equivalent to excluding radius<Rstar in that branch; candidate Rstar must be specified by its exact algebraic/KKT isolation, NOT equated to rounded C249 upper.

For ordered site trianglea,b,c, define squared sides X=|a−b|²,Y=|b−c|²,Z=|c−a|² and doubled signed area D=det(b−a,c−a)>0 under fixed faceorientation. Its circumradius condition is exactly
 **XYZ <=4 R² D²**.
Because ordinaryarea=D/2 andcircumradiusabc/(4area)=sqrt(XYZ)/(2D). Denominator positivity known. For covering radiusR<=U, pairseparationdelta implies
 **D >=delta³/(2U)>0**.
This provides uniform determinant gap on every siteface in relevant genuinecovers, ratherthan merely noncollinearity. Note D depends onchosenorientation; graphlist faceordersnotallCCW, orientcombinatoriallyonce.

For switchPi impose |Pi|²=1 and |Pi−ci|²=|Pi−c(i+1)|²<=R². These are polynomial constraints ofdegree2. Switchpositiveorientation determinedbyoutside-side oftheboundarysiteedge. Its doubledarea is d*height, withd>delta andheight>=1−sqrt(1−R²)>=R²/2>=9/128, so positivegap>=9delta/128 forinwardR>=3/8.

Sector chord Pi−Pprev length² W_i>qmin² and<=4R². Sectororientation nonnegative followsinwardnormbound; neednotdividebyitsarea andalphaπlimitsretained. Boundary cyclicorder canbe enforced withsuccessivechordturn determinantspositive andtotalwindingone; simplelocaldeterminantsALONE don'texclude multiplerotation/starpolygon, so use fixedangularsectors/explicitglobalorientation orpositiveflatmetricinterface. Do not silentlyreplaceglobalcyclicorderwithpairwise inequalities.

This polynomialencoding avoidsnear-zero circumradiusdenominators onsitefaces andexactlypreservesradiusinequality. It is NOT presently a complete lowdegree semialgebraic certificatebecauseglobalembedding/cyclicordering mustbeencodedandcandidateexactvalueisolated. A rigorous certificatecaninsteadstaywith C839/C841boundedanglevariables. Both representations compute the same siteface condition; use polynomialXYZ−4R²D² as independentkernel audit if implementing an anglecertificate.
