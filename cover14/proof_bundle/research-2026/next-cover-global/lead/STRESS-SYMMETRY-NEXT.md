# Next high-leverage stress obligation (not proved)

Independent numeric evidence: positive-support network44edges, 8facewitnesses. Two isolated components are X± plus their2anchors; remainingcomponent has12sites+8witnesses+8anchors. D2 averaging gives one remaining normalized symmetric stress parameter (`stress_symmetry_control.py`: rank36/37 numerically). Likely it controls relative mass between Xcomponents and thecentralcomponent.

Potential analytic method-limit theorem: NO fixed nonnegative sharp stress on this literal graph proves global lower bound via minimizedDirichletenergy onthecap-simplex. To establish, not merelyinfer fromoneHessian:
1. Ifany sharpstress has globalenergy≥r*², D2averagealso does: E_w(anchors)=min_free Σw_e distance² isconcave inw; invarianceandsaturationatcandidate imply averageisstillasharpcertificate.
2. Atanysharpstress, free-site/witness equilibrium plusnonnegativeweightsforces6zero faces (STRESS-SUPPORT-ANALYTIC.md). D2symmetricremainingcentralstresslikelyunique up toscale; establishwithanintervalnonzero minor oflinearstationarityequations, treatingexactrootsasinputs. Noexistenceproofneededforanecessaryconstraint.
3. Forcentralmass>0, findcapcritical tangentwithnegative energysecondvariation UNIFORMLY onallpossiblecentralstressweights. Mayusefixedrationaltestvelocitiesforallfree nodesinstead ofdifferentiatingSchur: stationaritykillssecondaccelerationtermsatfreenodes; anchoracceleration−|vtheta|² anchor contributes exactly. Intervalevaluatequadraticform<0 afternormalizingcentralmass1.
4. Ifcentralmass=0, onlyX2-edgepathsremain; E∝sin²(gapX/2), globally MAXIMIZED atcap, so shrinkingoneXgap yieldsE<r² (othersabsorbangle), rulingoutglobalcertificate.

This would onlykillthefixedstresscertificatefortheliteralgraph, nottheoptimalcover, notthetopologyreduction, andnot piecewise/domainrestricted orotherstrengthenedcertificates. Itwouldjustifychangingmetricrepresentation ratherthanwastingglobalHessianboxes.

Currentevidence: `stress-curvature-control.json` tangent decreasesone4-gapblock andincreasestheother, holdsbothcapgapsconstant, curvature−.0057634 withfirstderivative~1e−15; finite differencesconfirm. Needverifycentralnormalizedweightuniqueness (numericrankdoesnotprove), deriveexactvelocityrationalcontrol, andboundallcoefficientsusingC1167 rootbox.
