# Same-arc inner-root replacement for arbitrary n12 covers

Level: analytic theorem; scope global[all covers at 0<r<1]. It does not imply a fixed active count or a contact graph. This rederives a general geometric fact appearing in the read-only n11 assembly; no n11 classification is used.

Let a radius-r disk centered at t u, ||u||=1, t>0, intersect the unit circle. Its actual intersection arc has halfwidth α∈[0,asin r], and
cos α=(1+t²-r²)/(2t).
The two radial roots with exactly the same arc are
ρ±=cos α±sqrt(r²-sin²α),
with ρ−ρ+=1-r², both positive. Every boundary-active center has t equal to one of these roots.

If t=ρ+, replace it by ρ−u. Write a=x·u and m=(ρ++ρ−)/2=cos α. For x∈D:
* If a≤m, then ||x-ρ−u||²-||x-ρ+u||²=2(ρ+-ρ−)(a-m)≤0.
* If a≥m, then ||x-ρ−u||²≤1-2ρ−m+ρ−²=r².
Thus D∩B(ρ+u,r)⊆D∩B(ρ−u,r). The boundary arcs are identical, including α=0 (a singleton) and α=asin r (double root).

Apply replacements independently to every boundary-active disk. Coverage cannot be lost; each disk's active/inactive status is unchanged, as is its actual boundary arc. No preservation of old Voronoi ownership or switches is asserted. New boundary-center norms lie in [1-r,sqrt(1-r²)].

After projecting all centers into D (FOUNDATIONS §1), an inactive disk has norm t<1-r: with t≤1 and r>0, nonempty intersection with the unit circle is equivalent to t+r≥1. Such inactive centers need no change. Therefore any covering at r≤U has a representative with k=9,10,11 boundary centers of the inner-root form and 12-k other centers in B(0,1-r). This is a genuine WLOG for existence, not for all minimizers or uniqueness.

Parameter interface (necessary and sufficient for existence): choose k∈{9,10,11}, r∈(0,U], angles θ_i modulo 2π, halfwidths α_i∈[0,asin r], set c_i=(cosα_i−sqrt(r²−sin²α_i))(cosθ_i,sinθ_i), and choose remaining centers ||h_j||<1-r. Impose actual full-disk coverage (a finite complete criterion is being developed separately). Any such tuple gives a cover; every original cover has such a tuple. Rotation allows θ_1=0 because boundary-center norm is positive. Relabelling allows cyclic midpoint order; equal midpoints are not silently excluded.

For a CLOSED relaxation one may allow ||h_j||≤1-r and count k only as selected boundary labels. Limit hubs may then become tangent, so the labels must NOT be read as an exact count of all active disks. Any lower bound on this larger closed set remains valid. This distinction matters for interval domain coverage.

Missing implication: these reductions alone do not exclude k=10 or11, force D3 symmetry, force saturation/no-overlap of the arcs, or establish the optimal radius.
