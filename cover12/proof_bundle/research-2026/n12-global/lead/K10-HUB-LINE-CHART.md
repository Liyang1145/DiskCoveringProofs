# Nonsingular three-parameter chart and algebraic core domain for two hubs

FixedU, a=1−2U>0, e0=3U−1. For distinct hubs use translation-free rotation/reflection/relabeling to write
h1=(x−s,y), h2=(x+s,y), s=d/2>0, x≥0,y≥0.
This is permissible: rotate hub separation horizontally; swap labels/reflect x to make midpoint x≥0; reflect y to make y≥0. Inactive constraints are (x+s)²+y²≤(1−U)² (the other follows). No division byd or atan is needed once this chart is chosen. Exposed arcs have centersπ and0, common halfwidthπ−acos(s/U); all branch directions fixed. The nearmerge bound d≤1/10, if certified, lets us restricts≥1/20.

## Exact core criterion
Let K=B(0,a). Squared-distance difference to h1 andh2 is4s(X−x); nearesth1 onX≤x, nearesth2 onX≥x. Maximum of their minimum onK is attained on∂K (lead/TWO-HUB-CORE-REDUCTION.md).

Case x≥a: allK has h1 nearest, hence K covered iff (x−s)²+y²≤e0².

Case0≤x<a: the two dividing-circle points are (x,±q), q=sqrt(a²−x²). At them common squared distance is s²+(y±q)². Their maximal value is s²+(y+q)². These must be≤U².
The only other maxima of a squared distance on a circular arc occur at that center's antipodal direction. The antipode ofh2 has X=−a(x+s)/|h2|<0≤x, so it is outside h2's arc. Forh1=0 its distance is constant a<U. For nonzeroh1 its antipode has X=a(s−x)/sqrt((x−s)²+y²). It belongs to h1's arc iff
 a(s−x)≤x sqrt((x−s)²+y²).
If this holds, additionally require (x−s)²+y²≤e0². Otherwise no antipodal condition is needed. The two endpoints condition and this guarded antipodal condition are sufficient and necessary, including their equality cases. Any remaining stationary point is the distance minimum, not a maximum.

For interval exclusion, avoid delicate branching by either certify infeasibility of the endpoints necessary condition, or retain the box; these tests are necessary and cannot remove a legal cover. Whole-core branches remain, including x≥a. For exact semialgebraic implementation the square root in the antipode guard can be squared only after checking signs; x≥0, so s≤x automatically satisfies it; ifs>x it becomes a²(s−x)²≤x²((x−s)²+y²).

## Elementary uniform bounds
The negative x-axis core point(-a,0) is always nearerh1. Thus (a+x−s)²+y²≤U² for every feasible box, yielding x≤s+U−a=s+e0. Also the two y-axis points show min(|(0,±a)−hj|²)=(x−s)²+(a±y)² (sincex,s≥0), whence (x−s)²+(a+y)²≤U²; in particular0≤y≤e0. This last bound eliminates most of the original angular/two-radius domain: the midpoint's transverse offset is at most3U−1, uniformly in separation.

Hence a convenient containing box is
s∈(0,U), x∈[0,s+e0], y∈[0,e0], (x+s)²+y²≤(1−U)²,
with the exact core filters above. The open s<U domain here is intentional: s≥U was already removed by K10-SEPARATED-HUB-REDUCTION.md (d≥2U). If one instead uses the core constraints alone and closes the inactive inequalities, one must includes=U: it is feasible only at(s,x,y)=(U,a,0), with h2 boundary-tangent. No global step relies on silently discarding that endpoint. This is not a proof thatx ory=0, only a compact nonsingular domain suitable for interval dual certification.
