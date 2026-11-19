<!-- SPDX-License-Identifier: MIT -->
# Native n=19 lower-bound reduction: fourteen boundary owners

**Scope.** These are necessary conditions, not a global proof or an
exclusion of the fourteen-owner branch. The argument adapts
[the n=27 translated-core lemma](../cover27/proof_bundle/research-2026-11/followup/proof.md).
Apply it to a normalized hypothetical cover of the closed unit disk by
19 radius-(U) disks at (U=1/\sqrt{13}), obtained using the strict
margin from a cover at some (r<U) as in that source. Here an owner is a
center whose clipped Voronoi cell owns a **positive-length** boundary
arc. The native normalization gives one connected arc per owner; disks
merely intersecting the boundary are **not** counted. Voronoi tie
endpoints are harmless. This note does not claim that the normalization
preserves a prescribed owner count of the unperturbed configuration.

## The five-disk input

Let (r_D(5)) denote the arbitrary-center minimum for five disks.
We use (q=30469/50000<r_D(5)), as follows from the **geometric
characterization** in Károly Bezdek,
[Über einige Kreisüberdeckungen](https://gdz.sub.uni-goettingen.de/download/pdf/PPN301416052_0014/PPN301416052_0014.pdf),
§2, printed p. 12, Eqs. (2)–(3). This is a literature dependency for the
five-disk input, not a native reproof of its geometric classification.
The paper sketches the reduction and refers to Bezdek's dissertation
for full details. We do not use the printed numerical approximation.

Write (x=1/r_D(5)), (s=\sin\alpha).
The characterization bounds (x) by the maximum over the real solutions
(P(x,s)=0) with (0<s<1), (\sqrt 2<x<1+2s), where the polynomial
(P) is transcribed below. It is harmless to include every root in the
admissible region instead of the largest root at each fixed (s).
Suppose there were such a root at (x\ge 50000/30469>\sqrt2).
Maximize (x) on the compact set defined by (P=0),
(x\ge50000/30469), (0\le s\le1), (x\le1+2s).
The three boundaries (s=0), (s=1), and (x=1+2s) have nonzero
values of (P) there, by the identities below. The boundary
(x=50000/30469) is not an obstacle to **increasing** (x).
At a maximum, (P_s=0), since otherwise the implicit function theorem
provides a nearby (s(x)) with larger (x), still admissible. Thus the
resultant in (s) must vanish. Its only possible factor in the range is
(Q(x)), whose Sturm signs at the threshold and at (+\infty)
are both (+++---+++). There are no roots in the range. In particular,
no disconnected component or root at the threshold has been dropped.

This independently checks the polynomial step, using Python with SymPy;
all coefficient and sign operations use exact integers or rationals.

```python
import sympy as S

s, x = S.symbols("s x")
P = ((80*s**2 + 64*s)*x**6
     + (-416*s**3 - 384*s**2 - 64*s)*x**5
     + (848*s**4 + 928*s**3 + 352*s**2 + 32*s)*x**4
     + (-768*s**5 - 992*s**4 - 736*s**3 - 288*s**2 - 96*s)*x**3
     + (256*s**6 + 384*s**5 + 592*s**4 + 480*s**3
        + 336*s**2 + 96*s + 16)*x**2
     + (-128*s**5 - 192*s**4 - 256*s**3 - 160*s**2 - 96*s - 32)*x
     + 64*s**2 + 64*s + 16)
Q = (625*x**8 - 800*x**7 + 22*x**6 - 1776*x**5 + 1665*x**4
     + 1360*x**3 - 3480*x**2 + 2112*x + 1296)
assert S.expand(P.subs(s, 0) - 16*(x-1)**2) == 0
assert S.expand(P.subs(s, 1) - 144*(x-1)**6) == 0
assert S.expand(P.subs(s, (x-1)/2) - x**2*(x-1)**2*(x+1)**4) == 0
res = S.resultant(P, S.diff(P, s), s)
assert S.expand(res + 2**62*x**8*(x-1)**12*(x+1)**20*Q) == 0
x0 = S.Rational(50000, 30469)
seq = S.sturm(Q, x)
expected = [1, 1, 1, -1, -1, -1, 1, 1, 1]
assert [S.sign(p.subs(x, x0)) for p in seq] == expected
assert [S.sign(S.Poly(p, x).LC()) for p in seq] == expected
```

## Translated-core and angle restrictions

Suppose there are fourteen owners. Sort their center norms
(D_1\le\cdots\le D_{14}), and write (t_i) for the half-angle of the
arc owned by center (i). Thus (\sum_i t_i=\pi) and (D_i>1-U).
Put (L=U(1+1/q)). The owners' radius-(L) disks cover
({|z|\le 1+U-L}). Indeed, if an interior (z) were farther than
(L) from every owner, the radius of a concentric subdisk lying in the
unit disk and avoiding the owners' radius-(U) disks could be chosen
strictly larger than (L-U=U/q). That would give a five-disk covering
with rescaled radius less than (q), a contradiction. The closed
radius-(1+U-L) disk follows by closedness.

In particular (D_1\le L). If (D_2>2L-D_1), take (z) in the
direction opposite the first center, with norm slightly larger than
(L-D_1). Then the first center is farther than (L), and the other
centers are farther than (L) by reverse triangle inequality. This
point is within (1+U-L) because (D_1>1-U) and (L<1).
Consequently (D_1+D_2\le2L). Thus (D_1<.733) and (D_2<.744).
Also (D_3\le L+.13<.863): otherwise only the first two inflated
disks could meet the circle (|z|=.13), and neither can cover it.
For two arc half-widths to sum to at least (\pi), their cosines must
sum to at most zero. Writing each cosine as
((D_i^2+.13^2-L^2)/(2\cdot .13 D_i)) yields
(D_1D_2\le L^2-.13^2), impossible since
(.722^2>.733^2-.13^2). If either disk fails to meet the circle it
cannot help; if either arc is a singleton the same inequalities apply.

Averaging the two squared distances from an owner to its arc endpoints
gives (t_i\le f(D_i)) for
$$
f(d)=\arccos\left(\frac{d+(12/13)/d}{2}\right).
$$
Here we used (\cos t_i>0) and bounded the owner's component along
the arc midpoint by (D_i). On ([1-U,\sqrt{1-U^2}]), (f) is
increasing and concave: its inner function is convex and decreasing,
and arccos is decreasing and concave for positive inputs. Both
(D_1,D_2<.744<\sqrt{1-U^2}), so Jensen gives
(t_1+t_2\le2f(L)<.172). All half-angles are below (.2811) by
the unit boundary arc bound. If at most eight of the other twelve
exceed (.18), their total with the first two is at most
(.172+8\cdot.2811+4\cdot.18=3.1408<\pi), impossible.
Hence at least nine have (t_i>.18), and norm (D_i>.772)
since (f(.772)<.18) and (f) is increasing up to (.772).

The scalar bounds use only rational comparisons and alternating
Taylor inequalities for sine and cosine on ([0,1]):

```python
from fractions import Fraction as F

q = F("0.60938")
k = 1 + 1/q
assert k*k/13 < F(".733")**2
assert F(".278")**2 > F(1, 13)  # D_i > 1-U > .722
assert 2*F(".733")-F(".722") == F(".744")
assert F(".722")**2 > F(".733")**2-F(".13")**2
a = F(".086")
assert (k+12/k)**2/52 > (1-a*a/2+a**4/24)**2
a = F(".2811")
assert (a-a**3/6)**2 > F(1,13)
a, d = F(".18"), F(".772")
assert (d+F(12,13)/d)/2 > 1-a*a/2+a**4/24
assert F(".172")+8*F(".2811")+4*F(".18") < F("3.14159")
```

## Area diagnostic, not an exclusion

The native n=27 total-area bound, applied with 22 center triangles and
14 boundary edges, has base (B=22\cdot3\sqrt3/(4\cdot13)
+14\cdot(.5-.0387)/13). With the native concave (G), the new
two-angle bound gives the upper estimate
(B+2G(.086)+12G((\pi-.172)/12)): concavity gives each group
maximum at equal angles, and the total increases with the first group's
sum up to the ungrouped mean. Numerical evaluation gives about
3.24345, still about 0.10186 **above** (\pi). This diagnostic is
not a certified closure of the fourteen-owner branch.

## A closed subcase: adjacent shallow owners with a distant third

Write (p_i=D_i v_i) for the first two centers, with (v_i) unit,
and let (\theta\in[0,\pi]) be the angle between their directions.
There exists a unit direction (w) with
(w\cdot v_1=w\cdot v_2=-\cos(\theta/2)): use the opposite of the
direction bisector, or a perpendicular if (v_1=-v_2).
For (z=sw), where (0<s<1+U-L), both squared distances are
strictly greater than
[
d_0^2+s^2+2d_0s\cos(\theta/2),\qquad d_0=.722,
]
because (D_i>d_0). If (D_3>L+s), every remaining owner is
farther than (L) from (z), by the reverse triangle inequality.
The translated-core cover therefore gives the necessary condition
[
\cos(\theta/2)<\frac{L^2-d_0^2-s^2}{2d_0s}.
]
If the right side is nonpositive, this subcase is impossible for
all directions.

If the first two owners are adjacent in the boundary cycle, their
shared boundary switch point lies within (U) of each center, so
[
4U^2\ge |p_1-p_2|^2
=(D_1-D_2)^2+2D_1D_2(1-\cos\theta).
]
It follows that
(\cos^2(\theta/2)\ge 1-U^2/D_1D_2>1-(1/13)/d_0^2>.9^2).
With (s=.013), the distance estimate already exceeds (.733^2>L^2).
Thus the two (L)-disks cannot cover (z), so a third owner must
reach it and (D_3\le L+.013<.746). This excludes adjacency combined
with (D_3\ge.746). In fact the same implication holds whenever
(\cos(\theta/2)\ge.9), without adjacency.

Separately, when (D_3\ge.780), use (s=.047). Because (L<.733),
the remaining owners cannot reach (z) even when (D_3=.780).
The distance estimate rules out (\cos(\theta/2)\ge.21), so the
angular separation must be strictly larger than (2\arccos(.21)).
For both tests (s<1+U-L), since (1+U-L>1-.733>.047).

```python
from fractions import Fraction as F

d0, Lmax, U2 = F(".722"), F(".733"), F(1, 13)
assert 1-U2/d0**2 > F(".9")**2
for s, c, threshold in [
    (F(".013"), F(".9"), F(".746")),
    (F(".047"), F(".21"), F(".780")),
]:
    assert 0 < s < 1-Lmax
    assert Lmax+s == threshold
    assert d0**2+s**2+2*d0*s*c > Lmax**2
```

This does not rule out the required shallow third owner, nor does it
rule out sufficiently separated first two directions. Consequently
it does not close the fourteen-owner branch.
