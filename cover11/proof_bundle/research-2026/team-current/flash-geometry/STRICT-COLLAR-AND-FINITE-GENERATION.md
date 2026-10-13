# Strict inward collar for the inner-root ring, and finite generation of cl U

Object: unit closed disk D; 0 < r < 1/2; nine **ring** disks B(c_i,r) of radius r that
cover bd D; M := sqrt(1-r^2) < 1. This is the inner-root representative of the
C450/C451/C464 reduction, so |c_i| <= M for every ring centre. Write

  U := {x in D : |x-c_i| > r for all i}      (strict hole; the two hubs must cover it),
  K := {x in D : |x-c_i| >= r for all i}     (closed safe set; cl U = K minus its isolated points, C458).

All statements below are analytic (no sampling, no certificate assumed).

## 1. Collar theorem (the MARGIN interface of HOLE-LINE-CONVEXIFICATION is automatic)

**Theorem 1.** Every x with 2M-1 < |x| < 1 is *strictly* inside some ring disk. Hence
U subset B(0,2M-1) and, since U ∩ bd D = empty (bd D is covered),
cl U subset B(0, 2M-1) subset int D. In particular bd D ∩ cl U = empty: boundary
tangency points of K are not accessible from U, and no target-boundary arc can be a
continuous extreme generator.
*Proof.* Fix x with |x| = s in (2M-1,1), put u = x/s in bd D and delta = 1-s in
(0, 2(1-M)). Let i be a ring index covering u: |u-c_i| <= r. Then

  |s u - c_i|^2 - r^2 = (|u-c_i|^2 - r^2) - 2 delta (1 - u.c_i) + delta^2,

which is the exact expansion of |su-c_i|^2 - |u-c_i|^2 = (s-1)((s+1) - 2u.c_i).
Using |u-c_i|^2 - r^2 <= 0 and u.c_i <= |c_i| <= M,

  |s u - c_i|^2 - r^2 <= -2 delta (1-M) + delta^2 = delta (delta - 2(1-M)) < 0.

So x is strictly inside the disk of index i. For the radial part with s = 1 use that
every u in bd D satisfies min_i |u-c_i| <= r, so U ∩ bd D = empty. Closing U gives
cl U subset B(0,2M-1). ∎
At r = 19/50: M = sqrt(2139)/50, collar radius 2M-1 = (2 sqrt(2139)-50)/50 = .8499731...
Remark: the bound is structural, not sharp -- for the certified 9+2 object the hole
depth function is at most .62231, far inside the collar. The collar bound is uniform in
the configuration; no attempt is made to improve it here.

## 2. Finite generation on a half-plane (extension requested)

**Theorem 2.** Let H be a closed half-plane with boundary line L. Then

  conv(cl U ∩ H) = conv(A_H),  where
  A_H := { p in cl U ∩ H : p lies on two distinct ring circles, or p in L and p lies on a ring circle }.

A_H is finite with |A_H| <= 2 C(9,2) + 2*9 = 90, and every p in A_H has |p| <= 2M-1 < 1.
*Proof.* Let K_H := conv(cl U ∩ H); it is compact and convex. Claim: every extreme
point p of K_H lies in A_H. Extreme points of the convex hull of a compact set lie in
the set's closure, so p in cl U ∩ H; Theorem 1 gives |p| <= 2M-1 < 1, so p is interior
to D and has room for local perturbations. Case analysis:
 * p in int H and p in U: then B(p,eps) subset U ∩ int H for small eps, so p is the
   midpoint of two points of cl U ∩ H: not extreme.
 * p in int H, p not in U: some ring constraint is active. If only one disk is active
   at p, take tau perpendicular to p-c_i: |p ± t tau - c_i|^2 = r^2 + t^2 > r^2, the
   other disks keep a strict margin and int H is open, so p ± t tau in U ∩ int H for
   small t: not extreme. Otherwise p lies on at least two ring circles: p in A_H.
 * p in L = bd H and p in U: B(p,eps) subset U, and moving along L stays in H, so p is
   a midpoint of two points of cl U ∩ H: not extreme.
 * p in L, p not in U: p lies on at least one ring circle, so p in A_H.
Hence ext K_H subset A_H subset cl U ∩ H, so K_H = cl conv(ext K_H) subset conv(A_H)
subset K_H; A_H is finite, so conv(A_H) is compact and equality holds. ∎
Accessibility is built in by the clause p in cl U, so no blind "K = cl U" is used: K
can have isolated safe points, they are exactly K \ cl U and are excluded. The
effective test for a candidate p is C458's: with active normals n_i = p - c_i,

  p in cl U  <=>  there is a nonzero v with n_i . v >= 0 for all active i
             <=>  the active normals lie in a closed half-plane through the origin,

and p is isolated in K iff no such v exists, i.e. 0 in int conv{n_i : i active}
(which forces at least three active normals). Equality/tangency cases are covered by
the quadratic term in C458, so cone-degenerate points are not lost. Because
|p| <= 2M-1 < 1 for every candidate, C458's standing hypothesis |p| < 1 is automatic
here -- this is the second use of the collar.

## 3. Structural use (one line, no new machinery)
For each closed half-plane H the set cl U ∩ H is covered by one disk of radius r iff
its convex hull is, i.e. iff the minimum enclosing circle of the **finite** accessible
set A_H has radius <= r. So on each side of a separating line the hub position is
eliminated (it is the MEC centre of A_H) and feasibility is a finite condition on at
most 90 points, with the target-boundary continuous candidates removed by Theorem 1.
This is the interface HOLE-LINE-CONVEXIFICATION.md asked for; it replaces its
(MARGIN) hypothesis and its own K-versus-cl U caveat in the inner-root representative.

## Scope guards
* Theorems 1-2 use |c_i| <= M and the covering of bd D by the nine rings: they are
  statements about the **inner-root representative**, not about arbitrary covering
  configurations.
* Theorem 2 handles the condition "one disk covers the hole on one side of a line".
  It does not make the two-centre condition on U convex, does not produce any lower
  bound for r, and says nothing about the hub positions beyond the MEC identity.
* The collar radius 2M-1 is not claimed optimal; only 2M-1 < 1 is used.
