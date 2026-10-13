# Exact two-hub core coverage and a three-parameter domain

Scope: two closed disks B(h1,r),B(h2,r), r>0, core K=B(0,a), a>0. No symmetry, distinctness or adjacency assumptions. This is a core-only characterization, not full D coverage.

## Boundary suffices for a union of two disks
If every point of S(0,a) lies in the union, then the whole K does. Here is a direct distance proof, avoiding a topological-hole claim. Let f(x)=min(|x-h1|²,|x-h2|²). An interior local maximum is impossible:
- if a unique location is nearest, choose a direction with nonnegative dot product against x-h, making that squared distance strictly increase by its t² term, while the other remains above its old value for small t;
- if both distinct locations are equidistant, choose a vector v perpendicular to h2-h1, with v·(x-h1)≥0 (choose its sign). Then v·(x-h2) is the same nonnegative number, so both squared distances strictly increase for t>0;
- duplicate locations reduce to the first case (at x=h choose any nonzero v).
Therefore max_K f is attained on S(0,a). This proves the assertion and also handles disks whose union is disconnected.

## Angular characterization
A hub of norm t=0 covers S(0,a) iff r≥a. A nonzero hub covers the full circle iff t+a≤r. It covers no positive arc if |t-a|≥r, with external/internal singleton equality distinguished as usual; the full-circle equality t+a=r takes precedence. In the remaining proper-arc case |t-a|<r<t+a, its covered arc has halfwidth
β(t)=acos((a²+t²-r²)/(2at))∈(0,π),
centered at the direction of h. Tangent point arcs may be included by β=0; an absent arc cannot assist coverage unless the other is full.

If neither disk covers the whole circle, let δ∈[0,π] be the smaller angular separation of their directions. Then their two proper closed arcs cover S(0,a) iff
β(t1)+β(t2)≥2π-δ.
Proof: place the arc midpoints at0 andδ. The two gaps between these midpoints have lengthsδ and2π-δ; both must be bridged by the sum of the two halfwidths. The longer-gap inequality implies the shorter one. Conversely those inequalities ensure each of the two midpoint-to-midpoint segments is covered. This also implies β1+β2≥π, hence at least one β_i≥π/2, recovering t_i²≤r²-a².

For the n12 k10 branch use a=1-2r<r and t_i<1-r (nonboundary status). Rotation and relabelling leave only (t1,t2,δ), with either t_i≤r-a=3r-1 (a whole-core hub) or the inequality above. Reflection can place the relative angle in[0,π]. This is an exact 3-parameter core domain, NOT a proof that hubs are antipodal (δ=π), equal-radius, both core-essential, or fixed.

The whole-core-hub branch must remain: another hub may be redundant for the core yet essential nearer ∂D. Therefore imposing proper arcs on both hubs would lose legal configurations.

## Polynomial replacement, no inverse trig required
One may instead apply the finite candidate criterion to the core, scaled by a: unique-center antipodes on S(0,a), the two-center bisector-circle intersections when they exist, and a fixed boundary point. There are no noncollinear triples, and the argument above rules out interior maxima. This gives a denominator-free semialgebraic version, including hubs outside the core where the bisector need not cross it. Do NOT transfer the lemma 'any pair bisector crosses the unit disk' to this smaller core unless both hubs lie in it.

Structural use: the exact core domain feeds the exposed-hub-union capacity inequality in HUB-UNION-CAPACITY.md. A lower bound uniform over this domain can eliminate the k10 class without fixing a contact graph. Such a uniform bound remains open.
