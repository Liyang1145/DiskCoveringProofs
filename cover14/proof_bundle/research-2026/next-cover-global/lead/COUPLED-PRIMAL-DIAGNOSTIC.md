# Coupled primal numeric result and identity warning

`coupled_primal_probe.py/json`: actualcandidate residuals<2e−15. All5starts optimize areaexcess to0ornegative~1e−9; manychangedradius/angleconfigurations. ThisisNOToptimumproof andmayrepresent a geometricisoperimetricidentity/constraint, notnewcoverobstruction.

There are55variables and21equalities (16faceangles,4hiddensites,1boundaryperimeter), beforebounds; dimension34. Realcoverpositionmodrotation has27parameters. The7extraangles maymeasureboundary noncyclicity: a flatgluedVoronoitrangulation with10boundaryanchors generally hasnoncyclic anchorpolygon. Itsarea isboundedby thecyclicpolygonwiththesame10sidelengths. summinorarc(theta)=2pi determinesunitcircumradius. Thus totalarea+segmentcaps<=pi couldholdidenticallyforALLflatpatches, independentofU, with equalityenforcingcyclicboundary. Ifso objective0is realizabilityratherthanradiusoptimality.

Need reconstructgeometryfromoptimized(beta,x,y), check allboundaryanchorsconcyclic, actualnearest/cellorientation andsitebounds, then testsmallerU. DoNOTpromote nearzeroarea/readings into covercertificate, localoptimality orglobalbound. Positivegapabsence isonlycalibration.

Potential missingnecessarycondition currentlyNOTimplemented: normalization |boundaryowner center|<=sqrt(1-U²). The local wedge enforceschordgeometrybutdoesnotfixowner'sradialposition relativecircle. Also nonadjacentglobalnearestinequalities notpresent. Thesearebearinginterfaces, notnumericalprecisionissues.
