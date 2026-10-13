# Division-free complex-polynomial form of C1252

This is a globally NECESSARY semialgebraic interface, not an unconstrained sufficiency claim.

At a boundaryswitch with common anchor radius a>0 and adjacent realface radius R, let c=cos(beta), t=sin(beta)>=0. Put
 G=(a−R c)+i R t, D²=(a−R c)²+R²t².
For each adjacent owner j, denote its other anchor radius b_j, owner angle alpha_j with C_j=cos(alpha_j), S_j=sin(alpha_j)>=0, and chordlength
 L_j²=a²+b_j²−2a b_j C_j, L_j>=0.
Put Z_j=(a−b_j C_j)+i b_j S_j, hence |Z_j|=L_j. Finally introduce nonnegative h_j with h_j²=1−L_j²/4 and H_j=h_j+i L_j/2. Since ownedarcs areminor, H_j=exp(i theta_j/2).

Where D L_u L_v>0, G/D=exp(i gammaA), Z_j/L_j=exp(i delta_(j,A)). Therefore C1252 implies the complex equality
 **G² Z_u Z_v H_u H_v + D² L_u L_v = 0.**
Its real and imaginary parts are polynomial equations in radii, cos/sin variables, chordlengths and h. Add c²+t²=C_j²+S_j²=1, t,S_j>=0, h_j>=0, L_j>=0 and the magnitude identities above. Actualclippedcovers alsohave a−Rc>0 byC1250. Endpointlimits preserve allpolynomialrelations, including D=0 or L=0, without evaluating atan2(0,0).

These polynomial equations may be weaker at collapsededges (becomezeroidentity); retain compactanglevariables if sharpdegeneracyexclusionneeded. Even onnondegeneratefreeassignments, equation determines angle sum modulo2pi: pi or3pi can both be algebraic branches inpermissivedomain. C1252 ray-orderproof selects pi foractualcovers; do NOTassertpolynomialequationsalone certifyglobalgeometry. For necessaryrelaxations extra branches are safe, thoughweaker.

At actualcovers angles/radii equations plusthispolynomialclosure haveunitcircle meaning C1251. No needtranscendentalatan evaluation insidea future interval polynomialkernel. This formulation simultaneouslyretains thetwoownerwedges and adjacentrealface; it cannotbe captured byindependentone-face envelopes.
