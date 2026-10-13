# Midarc-frame core obstructions for filled consecutive-owner polygons

This is a NEW mathematical lemma, not an edit to the live frozen SIX proof.
It assumes the same original boundary-owner arcs and embedded center-disk/
corner-starred-limit bridge as the previous triangular and quadrilateral
lemmas. No finite scan is a continuous coverage or embedding proof.

Put U=234701/1000000 and R=1-2U. Every original owner's boundary arc has
length at most 2asin(rho)<pi/6 for rho<=U, since
U<1/4<sin(pi/12); the last comparison follows from sqrt(3)<7/4.

Consider a fully filled embedded disk patch whose simple outer polygon
consists of k consecutive original owners, with k=3,4,5 or6. Let a be the
boundary anchor shared by the first two owners and b the anchor shared by
the last two. The intervening anchors span the arcs of k-2 intervening
owners, so their oriented unit-circle angle has length less than
(k-2)pi/6<=2pi/3. Choose the radial direction to the MIDPOINT of this
oriented anchor arc, not its first endpoint.

Each owner vertex is within rho of an anchor on this short arc: the first
uses a, the last uses b, and every intermediate owner uses one of its two
adjacent anchors. Relative to the midpoint direction each anchor's angle
has absolute value at most (k-2)pi/12. Consequently every outer center has
projection at least cos((k-2)pi/12)-rho. A filled simple polygon and all its
enclosed centers lie in the convex hull of its outer vertices; thus the
same projection bound holds throughout the filled patch. No assumption
of convexity of the polygon itself is needed. Corner shadows are included
by continuity of the embedded limits. Coincident anchors only shorten
the oriented arc and do not weaken the bound.

Use these conservative exact lower bounds c_k for the cosine:

- k=3: c_3=24/25<cos(pi/12).
  Indeed (2+sqrt(3))/4>(24/25)^2 since
  sqrt(3)>1054/625, checked by (1054/625)^2<3.
- k=4: c_4=4/5<sqrt(3)/2=cos(pi/6).
- k=5: c_5=7/10<sqrt(2)/2=cos(pi/4).
- k=6: c_6=1/2=cos(pi/3).

All patch centers therefore have x>=c_k-U.

For k=3 use SEVEN targets: the origin and all six vertices
(0,+/-R),(+/-sqrt(3)R/2,+/-R/2) of a rotated regular hexagon.
Their maximum x is sqrt(3)R/2<7R/8, and
24/25-2U-7R/8>0. Thus horizontal separation from every patch center
exceeds U.

For k=4 use SIX targets: the origin and the five vertices
(R/2,+/-sqrt(3)R/2),(-R/2,+/-sqrt(3)R/2),(-R,0)
of a regular hexagon with its rightmost vertex omitted.
Their maximum x is R/2 and 4/5-2U-R/2=3/10-U>0.

For k=5 and k=6 use FIVE targets:
O,(0,+/-R),(-sqrt(3)R/2,+/-R/2).
All have x<=0, and c_k-2U>0 in both cases.

In every set all targets lie in the closed core disk and every pair has
distance at least R>2U. Original boundary-owner disks cannot cover the
open core; finite closed-union closure supplies the limiting boundary.
No patch disk can cover any chosen target. Therefore respectively
7,6,5,5 DISTINCT ORIGINAL nonowner disks outside the patch are necessary.
Targets may be rotated to the actual midarc frame for each realization;
the argument is universal, not a fixed finite sampling of the core.

If S is the set of enclosed nonowner labels, at most26-B-|S| original
nonowners can be outside. This includes introduced outside and every
future label. Original disks keep distinct labels. Shadow labels can
only reduce availability. Hence any fully filled patch with fewer
available outside labels than the corresponding required target count
excludes the ENTIRE prefix and all continuations.

The seven-target triangle strictly strengthens the frozen six-target
triangle; the six-target quadrilateral strengthens the earlier five-target
quadrilateral. Pentagonal and hexagonal rules are additional. Recognition
must certify the EXACT simple outer cycle, full triangular filling,
face connectivity, edge incidence, Euler relation and vertex links, with
no other original boundary owner in the patch. An unfilled region is not
paid. All original irredundant counts B+9,...,26 and all original/shadow
placements remain in scope.

This lemma requires distinct source geometry own/publication, actual
complete-current semantics and independent final before formal adoption.
Do not modify or restart the live SIX chain; preserve every newer
candidate-root payment, exact history, LOCAL and old proof receipt.
