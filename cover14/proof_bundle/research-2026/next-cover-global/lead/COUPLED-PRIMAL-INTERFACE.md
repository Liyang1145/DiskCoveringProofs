# Next structural diagnostic: retain all face/anchor radii

Current all-face envelope dual still maximizes each local radiusinterface independently. To determine whether this missingconsistency is bearing, bounded localnumeric test on actualcandidate (notglobalproof).

Variables: beta_e∈(0,pi) for all29facets, x_f=Rf/U∈(0,1] all16realfaces, y_e=anchor_radius/U∈(0,1] all10boundaryedges. Each realface satisfies sum h(x_f,t_fe,beta_e)=pi where t=otherface x or boundaryanchor y. Eachhidden site sumincidentbeta=2pi. Atboundarysite set alpha_v=2pi−sumincidentbeta∈(0,pi). Its two adjacentboundaryanchors have distances U*y_prev,U*y_next fromsite, so chordlength
 L_v=U sqrt(y_prev²+y_next²−2 y_prev y_next cosalpha_v),
 theta_v=2asin(L_v/2), and perimeter sumtheta=2pi.
The relevant ownedarc isshort (priornormalization/capacity), hence this theta is the correct minorarc, not a chosen alternatebranch. Wedgearea=.5U² y_prev y_next sinalpha_v+.5(theta_v−sintheta_v).
Pairedarea onedge=U²x_f*t_fe sinbeta_e. Objective totalarea minuspi. Genuinecover maps to this system with objective0. It is only necessary until flatgluing/boundaryembedding/globalnearest conditions proved.

Bounded experiment: calibrate allconstraints at actualcandidate to1e−12, then SLSQP constrainedmax fromcandidate and4small perturbations, fixediterationlimit800. Positivefeasibleobjective diagnoses remainingrelaxation gap; numericalfailure/zero doesnotprovelocal/globaloptimum. This testswhethercommonradiusconsistency alone canexplain candidatepointslack, notcertificatecounts.
