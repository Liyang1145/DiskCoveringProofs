# Independent review of the 26-disk area argument

The independent numerical checker `check_area_independent.py` verifies the improved face-and-ear area inequality for every boundary count b=14,...,26 at r=228081/1000000. It uses rational arithmetic, a Machin-formula enclosure of pi, alternating Taylor bounds, and integer square-root bounds. The smallest verified gap is at b=17 and is greater than approximately 0.0001304875. A negative control at r=23/100 correctly refuses to certify b=15,...,19. The script checks the scalar inequalities, not the geometric proof.

I also reviewed `coupling/TOPOLOGY.md`: the reflection, strict-slack normalization, connected boundary arcs, abstract Voronoi dual, and Euler face count fit together as described below. I found no counterexample. The argument depends on the written geometric and topological reasoning; a successful arithmetic script by itself does not prove that reasoning.

## Normalization and slack

Suppose disks of radius r0 cover the unit disk D. Pick r>r0 and put R=sqrt(1-r^2). If a center c has norm d>R, set lambda=R^2/d^2 and c'=lambda c. For every x in D,

    |x-c'|^2-r^2 = lambda (|x-c|^2-r^2) + (1-lambda)(|x|^2-1).

Thus each point covered by the old radius-r0 disk is strictly covered by the new radius-r disk. Centers already inside R are unchanged. Compactness of D gives uniform positive slack for this finite collection, so the centers can be moved slightly into the open radius-R disk and placed in generic position without losing coverage. In particular, they may be made distinct, with no four cocircular and no three Voronoi sites tied on the boundary. This reflection preserves the part of the old disk in D; it does not assert that all distances from the new center decrease.

Let m<=26 denote the resulting number of distinct centers. Each center is an interior point of its own restricted Voronoi cell. For two centers strictly inside the radius-R disk, their perpendicular bisector has distance h<R from the origin; its intersection with the unit circle is a chord of length greater than 2r.

Every boundary ownership point of a site lies in its own covering disk, whose boundary footprint has angular length at most 2 asin r<pi. If ownership of one cell had two separated pieces within that footprint, some competitor would beat it between two ownership points. The competitor's two bisector-circle crossings would lie between those points, hence inside a single footprint and at distance at most 2r, contrary to the chord bound. Genericity excludes isolated degenerate boundary contacts. Consequently every boundary cell owns one positive-length arc. Their number b satisfies 14<=b<=m<=26 because r<sin(pi/13).

## Topological and area interface

Restricted Voronoi cells are convex and contain their sites. Draw the abstract dual in the disk by connecting sites inside each cell to chosen interior points of common cell edges, and to their boundary switching points. The edges can be drawn without crossings inside each convex cell. Interior Voronoi vertices yield triangular faces on three sites. Each boundary switch q_i gives a face (q_i,c_i,c_{i+1}); each owned boundary arc gives a face (c_i,q_{i-1},q_i). This is an abstract triangulated disk with m interior site vertices and b boundary vertices. Its edges may be replaced by straight segments for area accounting: the resulting affine triangle images need not remain embedded and may overlap or reverse orientation.

Euler's formula and the edge-incidence count give F=2m+b-2 total faces, of which 2b are the two types of boundary face. Thus the number of interior site triangles is T=2m-b-2<=50-b. Each interior face corresponds to an interior Voronoi vertex that has equal distance at most r from its three sites, so its area is at most 3 sqrt(3) r^2/4. Each boundary-switch face has two sides of length at most r and hence area at most r^2/2.

The affine images of the abstract triangles cover the polygon bounded by the q_i: their signed winding numbers sum to the boundary polygon's winding number. Closedness covers the polygon edges. Add the b circular segments between that polygon and the unit circle. Overlap or reversed affine faces do not invalidate the upper bound by the sum of absolute areas. For an owned arc of angle 2 delta, write s=sin(delta) and z=sqrt(r^2-s^2). The two boundary endpoints are in the owner's disk, so its corresponding boundary triangle has area at most s z. The circular segment has area delta-s cos(delta). Therefore

    pi <= (50-b) (3 sqrt(3)/4) r^2 + b r^2/2 + sum_i g(delta_i),
    g(delta)=delta-sin(delta) cos(delta)+sin(delta) sqrt(r^2-sin(delta)^2).

The arcs partition the boundary, so sum_i delta_i=pi and each 0<=delta_i<=asin r. The circular segment and boundary triangle are permitted to overlap; adding their absolute areas is still a valid upper bound. An alternative is to use the oriented area chain directly, pairing each signed boundary triangle with its circular segment.

## Paired-face deficit

Each switching face has a site-site edge on the boundary-site cycle. Since each site owns a single arc, the cycle has b distinct site vertices. For b>=14 each cycle edge belongs to exactly one switching face and has exactly one face on its interior side; that other face is an interior three-site triangle. An interior triangle can meet at most two cycle edges: three would require the entire cycle to have only three vertices. This argument concerns the abstract planar triangulation and does not assume that its straight-line images are embedded.

Let L be the shared site's edge length and put h=sqrt(r^2-L^2/4). The switching face's third vertex q has distance at most r from both edge endpoints, so its area is at most Lh/2. The three vertices of the adjacent interior triangle lie in a common radius-r disk; its center lies at distance at most h from the line through the shared endpoints, so the triangle's altitude is at most r+h and its area is at most L(r+h)/2. For x=L/r in [0,2], the sum is therefore at most r^2 f(x), where

    f(x)=x/2+x sqrt(1-x^2/4).

With y=sqrt(1-x^2/4) and w=37/100, Young's inequality 2xy<=w x^2+y^2/w followed by completing the square yields

    f(x)<=1/(2w)+1/[8(1/(4w)-w)]=147325/83694.

Since sqrt(3)>433/250, the separate face bounds exceed this joint bound by more than 19/500 times r^2; their rational difference above that threshold is 30067/41847000.

For an interior triangle incident to two cycle edges, allocate both corresponding switching triangles to it. Let their shared-edge lengths divided by r be x1,x2, and define g(x)=x sqrt(1-x^2/4)/2. The first pair estimate bounds A+C1 by r^2 f(x1), and the other switching triangle by r^2 g(x2); reversing the two roles and averaging gives

    A+C1+C2 <= (r^2/2) [f(x1)+g(x1)+f(x2)+g(x2)]
                 <= r^2 max_{0<=x<=2} [x/2+(3/2)x sqrt(1-x^2/4)].

Young's inequality with w=101/250 and completing the square bound the maximum by `7377125/3286944`. The independent old bound for these three faces is `(3 sqrt(3)/4+1)r^2`; using sqrt(3)>433/250, its difference from this maximum exceeds `(54/1000)r^2` by the exact positive rational `51607/82173600`.

Assign each switching face to its unique neighboring interior triangle. If N1 and N2 interior triangles receive one and two cycle edges respectively, then b=N1+2N2. Their total area deficit is strictly greater than `(19/500)N1 r^2+(54/1000)N2 r^2`, which is at least `(27/1000)b r^2`. Every actual face occurs in just one such group, so no deficit is subtracted twice. The strict inequality is weakened to a non-strict subtraction, which is safe.

## Concavity checked independently

For 0<delta<asin r, set s=sin(delta), c=cos(delta), z=sqrt(r^2-s^2). Direct differentiation gives

    g' = 2s^2 + c(r^2-2s^2)/z,
    z^3 g''/s = 4c z^3-r^4-3r^2+6r^2s^2+2s^2-4s^4.

Since c z^3<=r(r^2-s^2), -4s^4<=0, and 6r^2+2-4r>0, the right-hand side is at most r^2(5r^2-1)<0 when r<1/sqrt(5). Continuity extends concavity to the endpoints. Jensen then bounds the final sum by b g(pi/b).

At r0=228081/1000000 all 13 resulting improved upper bounds are rigorously less than pi. They are continuous in r near r0, with strict domain margins sin(pi/14)<r0<sin(pi/13) and r0<1/sqrt(5). Hence the same inequalities hold at some slightly larger r. A hypothetical cover at radius r0 can be normalized using that larger radius and leads to a contradiction. Projection of centers to D and compactness give attainment of the optimum, so the argument yields r_D(26)>228081/1000000, subject to the written geometric proof above. The main proof may state the slightly weaker rational lower bound 2851/12500 using this number directly as its larger testing radius.

Run `python check_area_independent.py` for the positive scalar check and `python check_area_independent.py --negative-control` for the deliberately unsuccessful radius-23/100 check. The latter is a failure of this upper-bound certificate and does not prove that radius 23/100 is feasible.
