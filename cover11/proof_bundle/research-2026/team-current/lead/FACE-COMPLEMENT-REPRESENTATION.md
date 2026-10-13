# Face-source complementary-angle representation

Put T=b1+b2, D=b1-b2, A=b1-delta,B=b2+delta; A+B=T. On face1, the own sourcevector is 2r sinA(cosA,sinA). The OTHER Cartesian sourcevector divided by2r is
 X=sinA cosA+cosT sinD,
 Y=cos²A−cosT cosD.
On face2, exchange A→B and the sign of cosT sinD:
 X=sinB cosB−cosT sinD,
 Y=cos²B−cosT cosD.
These follow by expanding v=r(sin2b1+sin2A),t=r(cos2A−cos2b1) or reflectedface2 and subtractingotherQ. No division bycosT, so the coincidentcircle interface is regular.

At exactT=pi/2, 0<A<pi/2 by wedge and B=pi/2−A. The other vector is cosA(sinA,cosA), so its norm iscosA and angle pi/2−A. BOTH face terms become explicit smooth sine/angle functions; no sqrt/atan2 remains. Thus entirecommonfacearc, notmerelyridge, is parameterized by(r,b1,A) with b2=pi/2−b1,delta=b1−A,H=2r sin(b1+A). WedgeA∈(0,pi/2); closure[0,pi/2] is a safe extension. Normdisk retainsdirectresidual H²−2s cosdelta H+2r(1−r)≤0.

The linearhubterm reduces r*v since sin²b1+sin²b2=1 and sinb2cosb2−sinb1cosb1=0. coincident_face_jet.py implements this continuous extension including endpointA=0/pi/2; thosephysicalpolesarenormillegal, andsmoothformulaextensionisallowedforMVT.

check_face_complement.py verifies6 value+gradient controls against originalpolarface objective and3 exactcoincidencesubstitutions. GeneralformulasrequirelegalownA∈(0,pi), but genericotherangle still uses atan2 and can refuse. No claimofallmaximaoncoincidencesurface.
