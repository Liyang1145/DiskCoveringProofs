# Endpoint elimination at fixed viewing angle AND arc

Analytic exploration, no bearingclaim yet. Fixedα∈(0,π),θ∈(0,2asinr], let v=sin(θ/2), σ=sin(α/2), κ=cos(α/2). Endpointlengths a,b≤r have chordrelation 4v²=(a−b)²+4abσ². Wedgearea = ab sinα/2+g(θ)/2, so maximizep=ab.

Put a>=b byreflection. Since(a−b)²>=0, p<=v²/σ²; equality a=b=v/σ. If v<=rσ this is feasible and largestproduct. If v>rσ, equalendpoints infeasible, but feasibility requires v<=r/2 or? Generalmaxchord overbox ismax(r,2rσ), so for v>rσ, necessarily2v<=r andσ<1/2. The endpointcorner(r,0) produceslongchordbutzeroarea. For thisregime rootrelation at a=r gives b=r cosα±sqrt(4v²−r²sin²α). Need identifywhichroot yieldsmaxp withb<=r.

For fixedp, chord implies a²+b²=4v²+2p cosα; a²,b² roots. Constraintmax(a²,b²)<=r² imposes4v²+2p cosα+sqrt((4v²+2p cosα)²−4p²)<=2r². Forv>rσ, as p increasesfrom0, a²starts4v² andgrows? derivativepositivewhen cosα>0. Then maxp occursa=r, and validroot b=r cosα−sqrt(4v²−r²sin²α) (theplusroot>r inthisregime). Thus pmax=r²cosα−r sqrt(4v²−r²sin²α), nonnegativeiff2v<=r. Atv=rσ the lowerroot isr(2cosα−1), notr, indicating a DISCONNECTED feasibleproductbranch: equalendpointsolution boundary doesnotcontinueintounequal regime. This merits careful validation beforeuse; legal(α,θ) domain maycontain gaps in attainablep.

This representation exposes why separateθandα bounds remain loose andwhycornerbranches formnonconcaveenvelopes. A rigorous normalizednormcondition may eliminate the smallproductbranch forsmallα. Next duty is classifyfeasibleendpointpairs analytically, notassumeasymmetriccase iscontinuousfromsymmetriccase.
