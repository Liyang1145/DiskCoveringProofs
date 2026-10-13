# Correct polar plus-root exclusion (supersedes the rejected C864 evidence)

Scope: r∈[3/8,19/50], bj∈[1,acos r], Cartesian face disks C858 and norm boundary (v-s)^2+t^2=(1-r)^2, s=sqrt(1-r²). No objective claim. Write H²=v²+t² and v=H cosδ.

1. ANY face disk yields v<=r sin(2bj)+r<=2r<=.76<s, since s>.924. This excludes the Cartesian far half, NOT yet the polar plus root.
2. Face1 has vertical centre -r cos(2b1), hence t>=-r(1+cos(2b1)). Face2 has vertical centre +r cos(2b2), hence t<=r(1+cos(2b2)). Since 2bj∈[2,pi], cos(2bj)<=cos2<-2/5, so -.228<=t<=.228. Each side follows from one face disk; together give |t|<=.228. No grid or wedge needed.
3. Norm boundary and v<s give v=s-sqrt((1-r)^2-t²). We have s<.928, 1-r>=.62, and .62²-.228²=.332416>.576²=.331776. Thus v<.928-.576=.352<1/2.
4. The POLAR plus root H=s cosδ+sqrt((1-r)^2-s²sin²δ) implies H>=s cosδ. Multiply by H>0 to get H²>=sv. On norm boundary H²=2sv-2r(1-r), so v>=2r(1-r)/s. Uniformly this is > (2*(3/8)*(31/50))/(116/125)=465/928>1/2. Contradiction with step3. The discriminant-zero case is included in >= and is excluded as well.

Exact analytic constants: Taylor upper cos2 <= 1-2+2/3-4/45+2/315=-131/315<-2/5 (alternating decreasing terms, next term negative); s>.924 and s<.928 checked by squaring against endpoint 1-r². No sin2 Taylor bound is needed.

This removes only the polar PLUS norm-circle branch at high bearings. Both roots remained present in C863's polar certificate and its independent Cartesian control; neither C863 nor any active kernel relies on this lemma.

Audit of discarded member notes: the earlier proof confused v=s±sqrt(...) with H=s cosδ±sqrt(...), had an incorrect sine Taylor direction, and incorrectly described physical hub norm. The attempted correction also confused H with v and treated a directly provable t-cap as a sampling observation. None of these expressions is used here.
