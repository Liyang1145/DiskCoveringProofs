# Exact mechanism of six zero face weights at the sharp D2 candidate

Conditional analytic statement: the exact candidate satisfies the radical branch equations in root_scout.py, the listed contacts, and signs certified below separately. Numerical evidence cannot assert that algebraic root exists; root isolation remains independent.

A,A_y denote(a,b), C=(c,d), x-boundary ringX=(s,0), x-hubZ=(z,0), y-hubT=(0,t), allpositive. Weightsnonnegative; every free site and every free circumcenter witness isforce-balanced. For anacute3-siteface, itswitnessbalance is equivalent to weights w_i=t_f beta_i, t_f≥0, with beta_i>0 barycentriccoordinatesof itscircumcenter. Thus a singlezeroedge forces allthreefaceedgeszero. Acuteness NEVERforces allweightszero byitself; itallowspositivebalance.

## First cascade: four X-adjacent tight faces
The boundaryanchors of X are(s,±r), because s²+r²=1 and X hasmaximalarcwidth. Theirvectors fromX havezero xcomponent. The onlytightwitnessfacesincidenttoX are(X,(a,b),Z) and(X,(a,−b),Z). Theircircumcenters have xcoordinate(s+z)/2=a, sinceX,Zlieonx-axis. AtX eachwitness forcecomponent (X−w)_x=s−a=(s−z)/2>0. Hence X-site x-equilibrium withnonnegativeweightsforcesbothX-witnessedgeszero. Acute-facebalanceforcesbothentirefaceszero. Reflectiongives4zero faceweights total.

## Second cascade: two central tight faces
After thoseedgesvanish, Z=(z,0) isincidentto witnesses of (Z,(a,±b),(0,±t)), and centralfaces(Z,−Z,(0,±t)). The formerwitnesses are exactly(z,±r): b=r+sqrt(r²−(a−z)²) and t=r+sqrt(r²−z²) giveequalr distances to all3sites. Theirx-force atZ iszero. Centralfacewitnesseshavex=0 bysymmetry, givingpositive x-force z>0 atZ. Therefore bothcentraledgesatZ, and byacute-facebalance bothcentralfaceweights, vanish. Total6zero faces=18zero witnessedges.

This is a GLOBAL site-force obstruction togetherwithpositivebarycentrics, not a localwitness inabilitytobalance. ItdoesnotrequiregapKKT, merelysite+witnessstationarity andnonnegativeweights; capKKT remainsnecessaryforthecompleteenergyminimum test.

## Consequences and limitations
ThetwoX sites eachremain a2-edge anchorpath. Theremaining8tightfacewitnessesconnecttheother12sites to8non-X boundaryanchors. ZeroedwitnessnodesareremovedbeforeSchurelimination. Thepositive-supportnetworkmaythereforedecomposeinto3anchoredcomponents; thisdoesNOTinvalidateDirichletenergy or proveglobalcurvaturefailure. Sumcomponentenergiescanstillhaveusefulgapconvexity. Strictpositivityonoriginal62edges is mathematicallyimpossible, but positivityon44survivingedgesisnotexcluded.

Numeric independentrepresentation `stress_barycentric.py`: exactrationalliteralcoordinates→mp80→positivebarycentrics(min .14638)→float64linearprogram. CorrectgapKKTg_k=c−mu_k atuppercaps feasible. Fullmatrixresidual~8.4e−15, sixforcedzerofaceweightsobserved bymax-weightLP. Numericalrank35of37columns, notcertified. NoconeorcurvaturetheoremregisteredfromthisLP.

Next: express reducedSchurenergy aschordweightedLaplacian of10anchors, then boundfullgapHessianoverP*, ratherthanmisreadingzeroedgesasmethoddeath.
