# Cover sufficiency without embedding, orientation, or general position

## Proposition (finite PL disk certificate)
Let K be any finite combinatorial triangulated closed topological disk. Assign a point p_v∈R² to every vertex, with repeated points permitted. Extend affinely on every triangle to a continuous map F:|K|→R². Suppose the boundary vertices in their combinatorial order trace a simple convex polygon P exactly once in cyclic order (not merely the same vertex SET). Suppose, for each triangle t, its geometric image F(t) is covered by disks B(c_i,U) from a common finite set of sites. Then P is covered by those disks. No positivity of triangle areas, no local injectivity, no angle ledger, and no interior-vertex flatness is required.

Proof: if x in interiorP were outside F(|K|), then F maps the whole disk continuously into R²\{x}. Thus its boundary loop is null-homotopic there, contrary to winding number1 of the polygon boundary. Hence interiorP⊂F(|K|). The image is compact, so P⊂F(|K|). This is an existence-of-preimage argument, NOT injectivity. Inverted faces may cancel in the degree sum but cannot remove every preimage. A point inF(|K|) belongs to the image of at least one triangle and is therefore covered. The same proof works for any boundary loop of nonzero winding throughout the target region.

## Application to augmented covering graph K+
Take real site triangles of K, virtual A_euv triangles, and owner v A_prev A_next triangles as in C1257, but now provide GLOBAL Cartesian vertex coordinates. The anchor boundary is an ordered inscribed unitcircle polygon whose consecutive arc gaps are in(0,pi). Require:
1. For each realtriangle with sitesu,v,w there exists a witnessO_f with |O_f-u|,|O_f-v|,|O_f-w|<=U. Equal distances/circumcircle are NOT needed for this sufficiency direction.
2. Every site-anchor incidence satisfies |v-A_e|<=U.
3. 0<U<1 and each owner is assigned to the minorcirclearc between its adjacent anchors.
There are no determinant-sign constraints and triangles may be arbitrarily degenerate.

Realtriangle proof: for x=sum lambda_i v_i, lambda>=0,sumlambda1, the exact identity
 sum lambda_i |x-v_i|² = sum lambda_i |v_i-O_f|²−|x-O_f|² <=U².
So one site coversx. This works for collinear/repeated vertices as well. Virtualtriangle proof: letM=(u+v)/2. Both |M-u|=|M-v|<=U by the triangleinequality throughA_e. The two triangles A_euM and A_evM are covered byu,v respectively bydiskconvexity. Ownertriangle is covered byits site directly byconvexity.

Thus the finite PL theorem covers the anchorpolygon, even if the drawn faces cross or overlap or some vertices coincide. Exteriorcaps arecovered bythe owners: for a sitev whoseU-disk containsboth endpoints onS1, v≠0 (U<1), the intersection withS1 is a singlearc definedby cos(t−arg v)>=(1+|v|²−U²)/(2|v|)>0, hence ofwidth<pi. The minorarc joiningthetwo endpoints lies inthisintersection, anditsconvexhull is thecap. This doesnotrequirevinsideD. Therefore the entireunitdisk iscovered.

## Scope and relation to previous interfaces
This is a SUFFICIENT Cartesian certificate, global over all coordinates satisfying the listed finite conditions, including collapsed/inverted/intersecting interior drawings. It strictly removes embedding/flatness obligations when coordinates are ALREADY given. It does NOT claim arbitrary formal beta/radius assignments possess compatible globalcoordinates: C1254/C1257 remain useful precisely to constructthosecoordinatesfromangles. Nor does this declare arbitrary degenerate angleassignments realizable.

Necessary normalizedcover data have realface circumcenterwitnesses≤U andsite-anchordistances≤U byC1172. Constantgraph compactlimits preserve those inequalities andCartesian continuity; iftheanchorcycle stayssimple withpositivegaps<pi, the sufficient implication above remainsvalid evenwheninteriortriangles collapse. Zero/repeatedanchors andnonpositivearcgaps need separateboundaryhandling. No newglobal lowerboundfollows: this is an exact weaker realizationcertificate, not an exclusion.

Key structural lesson: injectivity is unnecessary for COVERAGE. It was needed to call the drawing an embedded triangulation, a stronger conclusion than the originalcoverproblem requires. Work on polynomialCartesian certificates can use this weaker topologicalinterface ratherthanprove positivity of everytriangleorfullflatmetricdevelopment.

## Closed boundary version
Permit lifted anchorangles t_0<=...<=t_q=t_0+2pi with increments in[0,pi). Consecutive repeatedanchors producezeroedges; aftercontractingthoseedges, thedistinctanchorpolygon isconvex andtraversedonce. Thereareatleast3distinctpoints, sinceincrements<pi andsum2pi. The PLboundarystillhaswinding1 initsinterior. Zeroarcs addnocap; everypositivearc isminorandhasthesameincidentowner. Allpreviousarguments apply unchanged. Thus repeatedanchors areallowed in cyclicconsecutive blocks. No interiororientationconditionintroduced.

A facewitness condition is equivalently minimum-enclosing-circle radius<=U for its three sites; it is closed undercoordinatelimits (witnesses maybekeptinconvexhullofthesites). Therefore bothinteriorcollapse andweakboundaryrepetition areallowed, provided arcgapsremain<pi andonewinding/orderpreserved. Atour U<1/3, normalizedactual-coverownerarcs are<=2asinU<pi, so thearcgapstrictupperbound survivescompactlimits.
