# Family maximum tests (conditional, not arc-by-arc upper)

Relax to rectangular r∈[.379,.37999], b1,b2∈[L,1], L=.60946080763725372899, width endpoints substituted by C872. Original widthfloor feasibility W≥g is dropped after deriving L; this creates a larger family. Family gradients must NOT reinstate W≥g during deformations.

At a hypothetical >C873 maximum on one circle boundary, intersections with the other circles are impossible by C873, except identicalfacecirclesT=pi/2 which are treated separately. Normdisk/wedge/source interfaces are analyzed in LOW-BOUNDARY-ENDPOINT-COVERAGE.md. Thus awayfromT=pi/2 inactiveconstraints have strictslack and sufficientlysmallparameterperturbationsalongthecurrentcirclechartstayfeasible. At interior parameter r,bj the derivative must vanish; at closedparameterends useonlyfeasibleone-sidedimprovement. Parameterp circlearc stationarity stillnecessary.

AtT=pi/2 changingb1 byh,b2 by−h preservescoincidence, so gradientF_b1−F_b2 is the tangenttest (ifbothparameterdirectionsinsidebounds). Changingr also preservescoincidence. Arbitrarybjchange cannotbeusedthere. C874 independently boundsentirecommonfacearc andremovesthissurface ifallinterfacesusedcorrectly.

low_family_maximum.py usesfirstderivative sign tests. low_family_second.py independentdirectional2ndAD calibrates36pointsagainstfirstAD/FD; low_family_hessian.py addsbearingpositivecurvature,centeredgradient andstationaryTaylor bounds only forinteriorbearingmaxima. These cannotcertifyper-fixedbearingarcupper; outputscopeisfamilymaximizerexclusionconditionalonC873.

Experiments: firstfamilygradient10003eval753live; Hessian10003eval756live. Noexclusion, and neitherisregistered asbearingresult. No moreexpansionofthisrepresentation absentnewstructuralgain. Complementarysourceangle representation andexactT=pi/2certificateareseparate genuinelystructuralprogress.
