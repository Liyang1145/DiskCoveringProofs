# Norm/face boundary intersections depend on one bearing only

Physical r>0, s=sqrt(1-r²), norm disk center N=(s,0), radius 1-r. Face j center C=(r sin2b, sigma*r cos2b), radius r; sigma=-1 forface1,+1 forface2. Put V=N-C, d=|V|>0. Since |C|=r and s²+r²=1,
 d²=1-2sr sin2b.
Along e=V/d, the two circle intersections are
 X±=C+a e ± h J e,
 a=(d²+r²-(1-r)²)/(2d)=r(1-s sin2b)/d,
 h²=r²-a²,
where J(vx,vy)=(-vy,vx). For h²<0 there is no real intersection. h=0 is a tangent boundary, requiring explicit retention; no division by h is needed in the point formula. d>0 uniformly: d≥s-r>0 on r≤.38. This formula does not involve the OTHER bearing.

Check: |X-C|²=a²+h²=r², and |X-N|²=(a-d)²+h²=(1-r)². This is independent Cartesian verification of the entire intersection set, not an implicit root solver. The other face disk, wedge and legal bearings must still be imposed, so neither sign may be discarded based solely on numerical candidates.

Structural use after C871+C872: for both bearings≤1, objective on norm-face intersections reduces to (r,b1,b2) and two signs; width variables eliminated. Arc interiors remain to be bounded by stationary-value analysis or certified directional monotonicity. Numeric maxima ~28.10421268 on the both-low region occur at such intersections, but that observation does NOT prove endpoint domination. Existing generic 4D MVT and disk-penalty probes leave live boxes; do not treat corner-only bounds as full boundary coverage.
