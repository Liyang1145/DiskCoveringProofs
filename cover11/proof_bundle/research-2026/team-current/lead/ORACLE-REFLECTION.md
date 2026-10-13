# Canonical reflection, exact graph map and patch transport

Object: fixed51edge oracle of FIXED-SWITCH-SOC-REDUCTION.md, canonical h9 fan0..3, h10 fan4..8. This is NOT the raw chart with central rings2,6.

Define site permutation p(i)=4-i mod9 on ring sites, p(9)=9,p(10)=10. It permutes the11face sets, including swapping central faces0/4. An anchor Ui is incident to sitesi,i+1, so anchor permutation a(i)=3-i mod9. For canonical angle list theta0=0, form new anchors U'_i = Q U_{a(i)} where Q is reflection in the line of angle theta3/2. Thus new theta'_i=theta3-theta_{3-i} modulo2pi, increasing cyclically and theta'_0=0. Forward gaps obey Delta'_i=Delta_{2-i}, hence y'_i=y_{2-i}. This is an involution of P.

Apply the same Q to every free node and permute sites/faces as above. Every endpoint/face distance is unchanged; all51constraints biject. Therefore V(y')=V(y), without acuteness, symmetry of a minimizer, or C915. In particular inf_P V=inf_{P intersect {y3<=y8}}V because each orbit has a representative there. This halves domain volume but does NOT remove one dimension/parameter. Fixed points remain. Restricting a known patch to this half-domain inherits its certificate automatically; no full-patch inclusion is required.

For scalar stresses, anchor Schur weights transport by w'_(i,j)=w_(a(i),a(j)). Relabel edge alpha by site/face/anchor permutation. The free minimization bijects and the Schur identity follows by permutation. This gives reflected exact fields at no optimization cost. A certified patch Q transports to rho(Q); C916 and rho(C916) both valid, regardless of whether rational cube center or cube shape is fixed.

Independent analytic report r20-stress/ORACLE-SYMMETRY-REDUCTION.md v2 agrees after correcting its raw/canonical mix. Its phrase 'one less tree parameter' is not adopted: the domain remains8D. No assertion of candidate symmetry is needed.
