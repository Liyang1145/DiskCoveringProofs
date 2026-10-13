# Coupled radius caps: an elementary comparison principle

This is a local necessary-interface theorem, not global geometric realization.

Fix nondegenerate edge angles beta_e∈(0,π). Each real face f has radius R_f>0 and adjacent real-face or boundary-anchor radii T_fe>0. The real angle is
 gamma_fe=h(R_f,T_fe,beta_e)=atan2(T_fe sin beta_e,R_f−T_fe cos beta_e),
 and sum_e gamma_fe=π. For fixed beta, h is strictly decreasing in its first radius and strictly increasing in its second.

For ANY prescribed positive neighboring radii t=(t1,t2,t3), the equation sum h(x,t_i,beta_i)=π has a unique positive root F_f(t), iff sum beta_i<2π. Indeed atx→0+ sumh=3π−sum beta>π, atx→∞ sumh→0, and derivative<0. F is monotone in all neighbors, homogeneous degree1, continuous on positive inputs. If upper bounds T_fe<=M_fe are known, then R_f<=F_f(M_fe). Thus simultaneous iteration
 M_f^(0)=U,
 M_f^(k+1)=min(M_f^(k),F_f(M_neighbors^(k)))
 preserves valid radius upper bounds and decreases them. Boundaryanchor caps stayU unless separatelyimproved. Underconnectedpositiveinterfaces, zero caps can be treated bylimits. Positive lower caps are NOTasserted.

For uniformneighborcapsU this is C1227 ifsum beta>=π; ifsum beta<π, the positive root exceedsU so the min does not tighten. Thus the single-face envelope is the first sweep of a shared-radius consistency iteration.

Fixedanglecomparison: Suppose R and S solve all real-face angle equations on a connected face network and have R_anchor<=S_anchor at each boundarynode. Let max ratio R_f/S_f beM>1 attained atf. Allneighbors haveR_g<=M S_g, hence gamma_fe(R)<=gamma_fe(S); equalityofsumπ forces equalityalong everyincidentedge, so allneighbor ratios=M. Propagatingtoanchorgivescontradiction. Therefore R<=S. If equalanchorvalues, applybothdirectionsforuniqueness. For closednetworkonlycommon scaling remains. This is compatiblewithstandardcircle-patternlogradiusvariationalprinciples; no noveltyclaim.

Obstacle: beta unknown globally; β→0 eliminatesstrictness, and branch-and-boundoverall29edgesnotyettractable. The comparison theorem can still improve a coupled patch support: twoadjacentfaces need5angles, generalpatchneedsitsdistinctedgeangles. Needboundedmechanismtestbefore scaling. Atcandidate the2slackfacesareedge-disjoint andalltheirneighborsR=U, so firstsweepalreadyfindstheexactcaps andadditionaliterationdoesnotimprovethecandidatepoint. Othergraphs/anglepatternswithadjacentslackfacescouldbenefit.
