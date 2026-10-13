# Ring locality lemma: the ring's intersection graph is a subgraph of `C_9²`

Author: flash-structure (own derivation; lead's capacity idea, lift/circular details supplied here).
Scope: `r <= 19/50`, unit closed disk `D`, nine boundary disks with the arc-ledger property
(nine essential actual arcs, cyclically ordered, only neighbouring arcs overlap, multiplicity `<= 2`),
plus stationarity only of the arc structure. **No `o = 0` assumption, no `ρ`-monotonicity, no sampling.**
Status: **analytic proof**; replaces the withdrawn scalar-ordering attempt (retracted C784) and unifies
`THREE-RING-CONSECUTIVE.md` (now a pointer to this file).

## 0 Statements

Index distance `g(i,j) := min((i-j) mod 9, (j-i) mod 9)` (cyclic distance on the 9 indices).

**L1 (two disks, primary).** If `g(i,j) >= 3` then `B_i ∩ B_j = ∅` (the closed disks are disjoint in
the whole plane, not merely non-overlapping on `∂D`).

**L2 (three disks).** If three ring disks have a common point, their indices are cyclically
consecutive: `{i, i+1, i+2}`. Equivalently: a point of `D` lies in at most three ring disks and, if
three, in three consecutive ones.

**L3 (four disks).** No four ring disks have a common point.

**L4 (graph form).** The intersection graph of the nine ring disks is a subgraph of `C_9²` (the square
of the 9-cycle): edges only between index distance 1 (adjacent, always intersecting on `∂D`) and index
distance 2 (may or may not intersect).

*Consequence used downstream.* For the inner crossing `v_k` of the adjacent pair `(k,k+1)`:
`v_k ∈ B_k ∩ B_{k+1}`; hence `v_k ∈ B_j` is possible only for `j ∈ {k-1, k+2}` (mod 9).
Indeed `g(k,j) >= 3` is excluded by L1, and `j = k-2` is excluded by L2 because
`g(k+1, k-2) = 3` would make `{k-2, k, k+1}` a non-consecutive triple.

## 1 The single counting engine

Write `I_i` for the actual arc of disk `i` (half-width `t_i <= asin r`), and for a point `p` put
`J := ∂D ∩ B(p,2r)`.

**(A)** `∂D ∩ B(p,c)` with `c = 2r < 1` is a single arc of half-width
`h(a) = arccos((1+a²-c²)/(2a)) <= asin(c) = asin(2r)` for every `a = |p| >= 0`
(maximum at `a = sqrt(1-c²)`; `a > 1` gives a smaller value; empty for small `a`). So
`|J| <= 2 asin(2r) < π`.

**(B)** If `p ∈ B_i` and `x ∈ I_i`, then `|x-p| <= |x-c_i| + |c_i-p| <= 2r`. So **`p ∈ B_i` implies
`I_i ⊆ J`.**

**(C) staircase/lift.** Lift the family periodically: `L_{s+9} = L_s + 2π`, `R_{s+9} = R_s + 2π`, with
`L_s < L_{s+1}`, `R_s < R_{s+1}` (strictly increasing endpoints), `R_s >= L_{s+1}` (adjacent arcs
meet) and `R_s < L_{s+2}` (non-adjacent arcs are disjoint on `∂D`). Lift `J` to the component `J̃`
meeting a lifted arc `I_a`. Because `I_i ⊆ J` is connected, the lift of `I_i` meeting `J̃` lies inside
`J̃`. Two copies of one arc inside `J̃` would give `2π <= |J| < π`, impossible, so all lifted arcs
inside `J̃` have distinct indices. If `I_a, I_b ⊆ J̃` with `a < b`, then `J̃ ∋ L_a, R_b` and `J̃` is an
interval, so `[L_a, R_b] ⊆ J̃`; the staircase gives `L_a < L_s < R_s < R_b` for every `a < s < b`,
hence **`I_s ⊆ J` for all indices strictly between the extreme two** (in the lift).

**(D) capacity.** Let `T` be the set of actual arcs contained in `J`. Then
`2π = |∂D| = |∪_{i} I_i| <= |J| + (9-|T|)·2 asin r <= 2 asin(2r) + (9-|T|)·2 asin r`.
If `|T| >= 4` this gives `π <= asin(2r) + 5 asin(r)`, which is **false** for every `r <= 19/50`
(the right side is strictly increasing, with value `asin(38/50)+5asin(19/50) = 2.8122945974 < π`;
rational certificate `2.82506254 < 3.14159265` from the Taylor series with geometric tail bound).
**Hence `|T| <= 3` for every point `p`.**

## 2 Proofs

**L3.** Four disks with a common point `p` give four arcs in `J` by (B), i.e. `|T| >= 4`,
contradicting (D). ∎

**L2.** Let three disks with common point `p` have lift indices `a < b < c` in a common `J̃`
(distinct by (C)). If the triple is not consecutive then at least one lift index lies strictly between
two of them, and (C) puts that arc in `J`, so `|T| >= 4`, contradicting (D). ∎

**L1.** Let `p ∈ B_i ∩ B_j` with `g(i,j) >= 3`. By (B), `I_i, I_j ⊆ J`; lift both into a common `J̃`.
Let `s` be the number of ledger steps of the route *inside the window* `J̃` (the two lifted arcs are at
index distance `s` in the lift). Since `g >= 3` means `m = (j-i) mod 9 ∈ {3,4,5,6}`, **both** routes
have at least `3` steps and at most `6`, hence `s ∈ {3,4,5,6}` and in particular `s < 9`, so the
`s-1 >= 2` intermediate lift indices are distinct actual arcs (not copies of `i` or `j`). By (C) each
intermediate arc lies in `J`, so `|T| >= s+1 >= 4`, contradicting (D). ∎
(**Correction after lead review:** the earlier text said "`s <= 4`" — neither true (the in-window route
can have up to `6` steps) nor needed; only `s < 9` is used, and it follows from `m ∈ {3,...,6}`.)

**L4** is the restatement of L1 for edges; adjacent pairs always intersect on `∂D` (arc-ledger
property), distance-2 pairs are unconstrained by this scheme (with `|T| = 3` the count reads
`2π <= 2asin(2r) + 12 asin r = 6.405 > 2π`, no contradiction).

**Independence of L2 from L3/L1.** L2 also follows from L1 plus the clique structure of `C_9²`: three
indices are pairwise within cyclic distance `<= 2` iff they are cyclically consecutive (checked for
`n = 9` by the four cases above), and `C_9²` has clique number 3. Both routes are available; the direct
route (L2 above) needs only the staircase.

## 3 What this replaces, and why it is not the retracted argument

* The **retracted** C784 argument tried to order the scalars `ρ_j sin δ_j` along the ring; this fails
  because `ρ_j` may shrink faster than `sin δ_j` grows.
* The present argument is a **length/capacity count**: it never compares `ρ`'s, and it excludes
  configurations by showing that `>= 4` arcs would have to fit into the arc `J`, which is too short.
* It also **strengthens** the four-disk lemma: three already force a fourth arc into `J` (via the
  endpoint order) when they are non-consecutive, and two force two further arcs when their index
  distance is `>= 3`.

## 4 Consequence for the two-hub criterion and for the ring's Voronoi topology

* **O1 two-neighbour reduction (proved).** `v_k` can lie in `B_j` only for `j ∈ {k-1, k+2}`
  (see §0). Hence the tips lemma reduces to the two scalar inequalities
  `|v_k - c_{k-1}| >= r` and `|v_k - c_{k+2}| >= r` (indices mod 9) — a *proved* reduction, replacing
  the withdrawn claim; the component-wise sufficient conditions of
  `NEXT-OBLIGATION-JOINT-REDUCTION.md` §4b remain available as the tool for those two.
* **Scope note (C789, flash-compute).** The locality lemma is a *ring-only* statement (no hubs, no
  coverage), so it is unaffected by any ledger counterexample. Flash-compute's numeric counterexample
  to the *unrestricted* tips lemma has its failing disk at index `k+2`, i.e. exactly inside the
  predicted candidate set `{k-1, k+2}` — it therefore **corroborates** the reduction rather than
  contradicting it, and it shows that O1 must be stated for **cover-extendable** ledgers (their ledger
  cannot be completed: best residual two-hub MEC `0.6116 > r = 0.38`).
* **Voronoi cellulation (statement corrected after lead review).** Interior vertices carry at most
  three ring cells, and if three, they are consecutive. For a *skip-one chord* (a Voronoi edge between
  ring cells `i` and `i+2`) the correct statement is: **at least one** of its two endpoints involves a
  hub cell — not "both". Reason: an endpoint of that edge has cells `{i, i+2, t}` with `t` a ring or a
  hub; if `t` is a ring cell then `{i, t, i+2}` must be consecutive (L2 + the pair rule), forcing
  `t = i+1`; and **both** endpoints cannot have `t = i+1`, because the cell `V_{i+1}` is convex and,
  if it contained both endpoints of the segment, it would contain the segment, whose interior points
  are equidistant-nearest to exactly `i` and `i+2` — contradiction. Hence at most one endpoint is the
  ring-only "ear" `(i,i+1,i+2)` and the other one carries a hub. (The earlier text said "both ends must
  be capped by hubs", which is false: an `(i,i+2)` edge may end at the consecutive-triple vertex
  `(i,i+1,i+2)`, exactly as L2 allows.)
* The Euler count `v <= 11`, `e <= 21` of the lead's Voronoi note is unchanged; the gain is qualitative
  (which degeneracies can occur).

## 5 Sanity check (not a certificate)

Own instruments, 300 structured legal ledgers (`r ∈ {0.366,0.37,0.375,0.37998385,0.38}`) plus the
record configuration: `min(|c_i-c_j| - 2r)` over index distance 3 is `+0.432952`, over distance 4 is
`+0.624781` (lemma predicts `> 0`), while distance-1 pairs reach `-0.186306` (intersecting, as they
must) and distance-2 pairs happen to be disjoint here (`+0.342087`), which the lemma leaves open.
The lemma itself is proved analytically above; no sampling is used as evidence for it.
