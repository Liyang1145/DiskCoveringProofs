# GLOBAL ORACLE INTERFACE AUDIT

Independent audit of one **global** interface of the fixed-switch reduction, not a
re-check of the local certificates. Written in `research-2026/team-current/closure-geometry/`
(only file written).

**Audited object.** `lead/FIXED-SWITCH-SOC-REDUCTION.md` (§§2–6), claims **C905**,
**C908**, **C909**, **C910** and their evidence paths
(`CLIPPED-DUAL-STRAIGHT-EMBEDDING.md`, `DUAL-DISK-INTERFACE-AUDIT.md`,
`STRICT-EMPTY-FACET-COMPLETENESS.md`, `FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md`,
`LOCAL-CERTIFICATE-ASSEMBLY.md`, `Q0-CLOSURE-EXCLUSIONS.md`), plus
`interval_hub_boundary.py` / `low_corner_jet.py` where the geometry is pinned.

**Audit question.** Is the implication

```
   (G)   "for EVERY Δ ∈ P,  V(U(Δ)) ≥ R*"   ⟹   no true cover has r < R*
```

*really globally proved*, in particular the switch↔Delaunay/fan correspondence, the
MEC-necessity for non-acute faces, graph isomorphism / cyclic labelling,
degeneracies, and the width bound defining `P`?

**Route (observed, not guessed).** The task was delivered on the route
`math-cline2-flash-session-f61549f0`, model `cline-pass/deepseek-v4.1-flash`
(observed in the lead's message header). All claim/evidence reads below were done
directly on this filesystem; no unobserved route is asserted.

---

## 0. Executive answer

**(G) is SOUND — the implication itself has no hidden premise, provided the three
upstream class/canonical reductions it consumes are granted.** I found no missing
necessary condition, no converse assumption, and no orientation/labelling gap that
would break the implication. In particular:

**Scope of this "sound".** *Interface-level only*: given the declared upstream
class/canonical reductions, no step of the implication itself is missing. Everything
here is to be read as conditional on the upstream list in §2 (C450/C451/C464,
C818/C819/C820 and the k3/k4 closure certificates, C801/C802/C908, C892/C897/C902);
I did **not** re-audit those, so nothing in this note should be quoted as
"unconditional" for the whole chain.

* the relaxation direction is one-way and correct (every true cover supplies a
  feasible oracle point with `t = r`, so `V(U) ≤ r`), and the oracle drops only
  necessary conditions;
* the width domain `P` contains the width vector of every true cover (it is an outer
  domain, not the set of realisable width vectors), and the lower width bound `m` is
  *derived* from the upper caps, so it adds no relaxation;
* the MEC-form face constraint is necessary for **all** faces, acute or not (via the
  face's Voronoi witness), so the missing acuteness is a loss of *strength*, not of
  validity.

**However, the global obligation itself is OPEN.** `V(U(Δ)) ≥ R*` for every
`Δ ∈ P` is proved only in an **existential angular neighbourhood** of the candidate
orbit (C910). `min_P V ≥ R*` is therefore *sufficient and necessary for this proof
route*, not a hidden premise, but it remains an unproved global statement about the
8-dimensional polytope `P`. The load-bearing conditional inputs are the class
reductions (C450/C451/C464 inward-root 9+2, C818/C819, C820, and the q0 closure
dual certificates) and, for the *complement of the high-bearing region*, the
bearing/width eliminations.

---

## 1. The interface, written out exactly

Graph (canonical q0(6,7), after the lead's relabel `new ring i = old (i+2) mod 9`):
9 ring sites `c0..c8` cyclically, hubs `a` (fans over ring edges 0-3), `b`
(fans over 4-8), central faces `(c0,a,b)`, `(c4,a,b)`; 11 triangular faces.
Anchors `U = (U0..U8)` are the nine **nearest-cell boundary switches**
(`U_i` between `c_i` and `c_{i+1}` on `bd D`).

Oracle `V(U)`: minimize `t ≥ 0` over
`C = (c0..c8,a,b) ∈ R22`, `Z = (z_f)_{f=1..11} ∈ R22` subject to

```
   18 endpoint:  |c_i - U_{i-1}| ≤ t ,  |c_i - U_i| ≤ t         (i = 0..8)
   33 face:      |c_s - z_f| ≤ t   for the three vertices s of face f
```

(`z_f` free — this is the **MEC form**: a triple lies in some radius-`t` disk iff its
minimum enclosing radius is ≤ t).

**Necessity of the 51 constraints (the direction that matters).** Let the
configuration be a true `c`-cover with covering radius `r`, and let `V_Σ` denote the
finite set of Voronoi vertices of the refined (clipped) diagram plus the nine
boundary switches. Each witness point `x ∈ V_Σ` satisfies
`max_{s incident to x} |x - c_s| = dist(x,S) ≤ r` (this is the covering hypothesis
applied to `x`, not an equality claim about the covering radius). Reading off the two
witness types:

* **switches.** At the boundary switch `U_i` the two winning sites are `c_i, c_{i+1}`
  and each is at distance `≤ r`, so `|c_i - U_i| ≤ r` and `|c_{i+1} - U_i| ≤ r`;
  taking `i` and `i-1` over all indices gives the 18 endpoint constraints. The
  indexing is consistent (`c_i`'s two owned endpoints are `U_{i-1}` and `U_i`).
* **face vertices.** Each selected face has a Voronoi vertex `z_f` with
  `|z_f - c_s| ≤ r` at its three incident sites, so the triple fits in the radius-`r`
  disk centred at `z_f`: the 33 face constraints.

Hence the true sites together with those witness points form a feasible oracle point
with `t = r`, and therefore `V(U) ≤ r`. **No equality between `r` and the constraint
maxima is asserted, and none is used**: the switch distances need not be the maximal
ball radius and, for an obtuse face, the minimum enclosing radius is strictly smaller
than the circumradius, so a "`r =` max(endpoints, MEC)" identity would be false in
general and is deliberately not claimed here.

Three consequences I checked explicitly:

* the 18 endpoint constraints are necessary because `dist(·, c_i)` restricted to the
  open owned arc is maximised at an endpoint, and both endpoints are covered by
  hypothesis (each endpoint is a witness point);
* the 33 face constraints are necessary because each selected face corresponds to a
  Voronoi vertex `z_f` with `|z_f - c_s| ≤ r` at all three incident sites;
* **the oracle omits** (inward norm `|c_i| ≤ sqrt(1-r²)`, hub norm `|h| ≤ 1-r`,
  `z_f` = actual circumcentre, distinctness, "sites cover `D`", the Delaunay/
  Voronoi consistency of the 11 faces). Omitting necessary conditions relaxes the
  minimisation, so `V` only becomes **smaller**: the lower-bound direction is safe.
  The lead's §2 statement on this is correct. *This is the point where an incorrect
  claim would have broken (G); I found none.*

**Sufficiency of (G).** Assume (G). Let a true cover have radius `r`. Its widths
`Δ ∈ P` (Sections 2–3 below), so `V(U(Δ)) ≥ R*`. But necessity of the 51 constraints
gives `V(U(Δ)) ≤ r`. Hence `r ≥ R*`. With the exact candidate cover `C892` at radius
`R*` this pins the infimum. **This chain uses only the constraint-necessity argument
and (G); I found no extra premise.**

**Necessity of the form of (G).** `V(U(Δ*)) = R*` exactly at the candidate
(C909), so `min_P V ≤ R*`. Therefore any proof via this oracle must prove exactly
`min_P V ≥ R*`; the weaker `V(U) ≥ R*` on a proper subset — in particular the local
neighbourhood of C910 — does **not** close the global obligation. The lead's §6 is
correct on this and the file itself says so.

---

## 2. Interface-level checks and their upstream conditions

**No item in this section is "unconditional".** Every statement below is either
(a) an interface-level fact with no hidden premise *inside* the interface, or (b) a
statement that is conditional on the upstream class/canonical reductions it
consumes. The labels make this split explicit, and no claim here should be read as
"the whole chain is audited": I re-audited only the interface, not the upstream
dependents.

Labels: **[I]** interface-level: no hidden premise found in the interface itself,
*conditional on the 9+2 canonical form and fixed `q0(6,7)` graph being the class
under consideration* (i.e. on the items marked **[C-up]**); **[C-up]** statement
whose validity depends on the listed upstream claims/files, which I did **not**
re-audit; **[L]** local statement; **[O]** open.

**Upstream inputs consumed by (G) (declared, not re-audited):**
`C450, C451, C464` (inward-root 9-essential ring + 2 indispensable hubs),
`C818, C819, C820` and the k3/k4 closure dual certificates (q0 class exclusions),
`C801, C802` (clipped dual disk), `C892, C897, C902` (candidate, weights, local
optimality), `C907`.

**[C-up] Canonical class (C450/C451/C464 reduction).** Any hypothetical cover
`r ≤ 19/50` reduces to inward-root 9-essential ring + 2 indispensable hubs. I did
not re-audit this; it is the *first* consumer of (G) and is load-bearing.
*Dependency: C450, C451, C464.*

**[C-up] Oracle formulation and Slater.** 45 variables, 51 `ℓ2` constraints; the
graph is connected to the 9 anchors, so `t`-boundedness bounds every free node, the
feasible set is closed and attained, and `C=0, t > max|U_i|+1` is strictly feasible.
Strong conic duality then holds; the `ℓ2`-cone is self-dual. *Dependency on the graph
being the fixed `q0(6,7)` graph (see the [C-up] item below).*

**[C-up] Vector-force dual.** For any `p_e` with divergence 0 at every free node and
`Σ|p_e| ≤ 1`, every feasible point satisfies `Σ p_e·(X_v-X_w) ≤ t`, hence
`V(U) ≥ Σ_i l_i·U_i` with loads `l_i` determined by the anchors. Free-node
cancellation is exact. `V` is convex and positively homogeneous in the **Cartesian**
anchor coordinates, continuous and Euclidean-motion invariant; convexity does **not**
extend to the angular domain (the file says this explicitly — correct, and it is the
reason the outer problem is hard). The converse (sup of these bounds = `V`) uses the
SOCP dual and is [C-up] by the same dependency on the fixed graph.

**[I] Width bound (the "short arc" lemma).** A radius-`r` disk with `r<1` covers at
most one arc of `bd D` of length `≤ 2 asin r`, and a disk centred at `0` covers no
boundary point. Elementary: for a centre `d(cosφ,sinφ)`, coverage means
`cos(θ-φ) ≥ (1+d²-r²)/(2d) ≥ sqrt(1-r²) > 0`, so `|θ-φ| ≤ asin r`. Using the **whole
owned interval** (not just the endpoint chord) is what excludes a major arc; the
file's remark is correct. This is a direct geometric inequality, not a consumer of
the class reductions.

**[I] `P` is nonempty, `m` is derived, and `P` is an OUTER DOMAIN (not the true set).**
Numerically verified: `L = 2 asin(19/50) = 0.779592592948521`,
`m = 2π - 8L = 0.0464445635914175 > 0`, and `ΣΔ_i = 2π` with all `Δ_i ≤ L`
**forces** `Δ_i ≥ 2π - 8L = m`. So

```
   P = {Δ ∈ [m,L]^9 : ΣΔ_i = 2π}   ⊇   { width vectors of true covers } / rotation ,
```

and the `m`-lower bound is not an extra assumption but a consequence of the upper
caps. **`P` contains the width vectors of all true covers but is NOT the set of
achievable width vectors**: for a generic `Δ ∈ P` there need not exist any
configuration realising it, and `V(U(Δ))` is then the value of a formal SOCP only.
That is exactly the right (superset) direction for a lower bound — proving
`V ≥ R*` on all of `P` is the *stronger*, safe statement — but it must not be
misread as "every `Δ ∈ P` is a cover", and no conclusion is drawn from
realisability. Also `19/50 < sin(π/8)` (`0.1444 < 0.1464466...`), so `m > 0` is
exact, and `P` is a nonempty compact convex polytope of dimension 8.

**[C-up] Switch ↔ Delaunay correspondence (C905).** For two cyclically adjacent
boundary arcs, exactly one point of `bd D` is equidistant from the two centres and
covered by their disks; the arcs are essential (total length `≤ 16 asin r < 2π`), so
no containment, and the arc-radical-line picture gives `|p_in| < 1 ≤ |p_out|`. The
essentiality counting (`8·2 asin r < 2π`, i.e. `L < π/4`: `0.7796 < 0.7854`) is
elementary, but the statement is *relative to the established 9-essential
boundary-arc class*. **Consequence:** the 9 anchors are well-defined, distinct, and
in the cyclic order of the ring labels.

**[C-up] Combinatorial consistency of the fixed graph.** With `n = 11` sites of which
`m_int = 2` are interior (the two hubs) and the abstract boundary count is `h = 9`,
the disk triangulation has `F = 2 m_int + h - 2 = 11` faces and
`E = 3n - 3 - h = 21` edges; Euler `V - E + F = 11 - 21 + 11 = 1` (disk). Two
cautions: `m_int` counts **interior** sites only (not total sites), and `h = 9` is the
**abstract boundary count** of the dual disk (the nine ring labels), which need not
coincide with the number of vertices of the full convex hull of the 11 sites if some
ring site were hull-interior. Verified degree arithmetic: with `k` hub-ring edges,
`deg_a + deg_b = k+2`; the reduced cases correspond to the pairs
`(5,8), (8,5), (6,7), (7,6)` and `(4,9), (9,4)`, i.e. all nine ring sites
hub-adjacent. *This is a consistency check only; the pair enumeration and the
exclusions `(4,9)`, `(5,8)` come from C818/C819 and the closure dual certificates,
which I did not re-audit.*

**[I] Face-vs-candidate `z_f`.** `z_f` free is *only* a relaxation; no acuteness is
used at this stage. `C902` supplies the reverse-direction strictness **locally**
(hence [L]).

**[L] Switch labelling / isomorphism at the root (C909).** The relabel
`new ring i = old (i+2) mod 9` maps the root's central faces `(2,9,10),(6,9,10)` to
`(0,a,b),(4,a,b)` and hub9 to hub `a`; it is a cyclic relabelling, geometry
unchanged. C909 is **local** (`local[single exact anchor tuple]`) — I confirm its
caliber line, including that "every fixed-`U*` optimum has the candidate's 11 site
coordinates" is a *fixed-anchor uniqueness* statement, not a global one.

**[L] C910 is genuinely only local.** Its own caliber says "no explicit
neighborhood size and no global bound on the 8D angular polytope `P`". The
compactness/subsequence argument in `FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md` §4–5
needs the full 51-edge graph for path-boundedness (zero dual weights do not delete
primal constraints) — correct — and uses short-arc containment plus
acute-MEC=circumradius. **The acuteness premise is local and is NOT needed
globally** (see §3.3).

---

## 3. The four points the task asked me to attack

### 3.1 Switch ↔ Delaunay / fan correspondence

*Switch existence/uniqueness within the established class* is C905 (a declared
upstream input; I did not re-audit it). What is **not** established is the
claim that the *same* 11-face fan graph persists for every `U ∈ P`. Two separate
issues, both benign for (G):

1. **Which pairs are Voronoi/Delaunay adjacent?** `U_i` is a boundary switch, i.e.
   `c_i` and `c_{i+1}` are the two nearest sites on an interval of `bd D`. Then
   `c_i c_{i+1}` is a Voronoi adjacency **inside** `D` (their cells touch along the
   radical-line segment through `U_i`, and `U_i` has exactly two winning sites, so
   the common boundary is a genuine edge). Hence, after
   `CLIPPED-DUAL-STRAIGHT-EMBEDDING.md`, the realisation is an embedded straight-line
   simplicial disk whose outer cycle is the ring in arc order and whose 11 triangles
   are full Delaunay triangles. I verified the pieces of that argument that matter
   for the interface (subcomplex embedding, Jordan ⇒ image = interior, 11 = 2n-h-2),
   but the base facts are C801/C802/C908 and remain upstream inputs.
2. **Is the graph assignment still `(6,7)` for other `Δ ∈ P`?** The oracle *fixes*
   the graph. If some `U ∈ P` were realisable only with a different degree pair, the
   oracle might be non-tight there but is still a **valid lower bound** (it drops
   necessary constraints only). More importantly, the class reduction says the
   degree pair for `r ≤ 19/50` is one of the `(5,8),(6,7)` types with `(4,9)`
   excluded; only `q0(6,7)` survives the closure dual at `R = 3/8`. So for the
   configurations of interest the graph is the fixed one, provided the pair
   alternative `(5,8)` is indeed handled by the k3 certificate. *Dependency on
   C818/C819/C820 + the two closure certificates — declared, not re-audited.*
   **Interface verdict: sound conditional on those, but
   note the graph is fixed by the class reduction, not by the anchor tuple.**

### 3.2 MEC necessity for non-acute faces

The oracle uses `∃ z_f : |c_s - z_f| ≤ t` for `s ∈ f`. **Necessary for every
face**, acute or obtuse, and the reason is the witness structure: the face has an
associated Voronoi vertex `z_f` with `|z_f - c_s| ≤ r` at its three incident sites
(the covering hypothesis applied at `z_f`). Hence MEC `≤` circumradius gives the
constraint without any acuteness. So (i) dropping acuteness does not weaken
soundness, and (ii) using *equality* with the circumradius as the constraint (as the
local §5 does) is only justified **when acuteness is known**, which is why the local
argument needs the `>7/100` dot-product margin. Note the correct statement is
`MEC < R_circ` for an obtuse face, so no "`r =` max(endpoints, MEC)" identity may be
used anywhere. The file's §2 phrasing "these omitted constraints only relax the
problem" is correct for the face constraints too.
**Interface verdict: sound; no acuteness premise needed globally.**

### 3.3 Graph isomorphism / cyclic labelling

* The 9 ring labels are pinned by the boundary-arc order (C905 + C908); the two hub
  labels are exchangeable, and the canonical form `(0,a,b),(4,a,b)` is reached by a
  cyclic shift `i ↦ i+2` (C909 records exactly this). Since `V` is invariant under
  simultaneous rotation of the anchors, fixing `U_0 = (1,0)` loses nothing, and the
  width vector `Δ` is a complete rotation-invariant invariant of the anchor orbit
  (9 positive numbers summing to `2π` determine the orbit up to rotation).
* **Reflection**: the width vector also determines the orbit up to reflection; `P`
  is a *set of orbits*, and `V` is evaluated on one representative. A geometric
  configuration and its mirror image have the same `V` (the oracle constraints are
  mirror-covariant), so no double-counting or missing case arises.
  **Interface verdict: sound.** The one caveat is that `V(U(Δ))` must be well-defined
  on the orbit, which holds because the constraints are invariant under the overall
  Euclidean motion — verified from the constraint list (only differences
  `c_i - U_j` and `c_s - z_f` occur).

### 3.4 Degeneracies

* `Δ_i = 0` cannot occur (`m > 0`), so no anchor degeneracy from coincident switches.
* Cocircular sites / zero-length dual edges: `CLIPPED-DUAL-STRAIGHT-EMBEDDING.md`
  handles them (artificial diagonals only, no zero-length site edges, positive
  triangle areas). For the oracle this is irrelevant: `z_f` is free, so face
  degeneracy cannot make a necessary constraint vacuous.
* Distinctness: the oracle allows coincident sites (a relaxation). Not a soundness
  issue, but it means `V` can in principle be strictly smaller than the true optimum
  — that is exactly why `min_P V ≥ R*` must be proved rather than assumed.
* `t = 0` is not possible for a true cover but is allowed by the oracle; harmless.

### 3.5 The width bound `P` (and the one thing I checked hardest)

* `Δ_i ≤ L = 2 asin(19/50)` uses `r ≤ 19/50`, which is *given* for the class
  (the reduction is `r ≤ 19/50`) — not a hidden premise, and it is **not** weakened
  by using `19/50` instead of the true `r₀`: using the larger `L` only makes `P`
  larger, so `min_P V ≥ R*` is the stronger necessary statement.
* `Δ_i ≥ m` is derived (`ΣΔ = 2π` and 8 upper caps), so no extra hypothesis.
* **`P` is an OUTER DOMAIN, not the set of achievable width vectors.** It contains
  the width vector of every true cover, but a generic `Δ ∈ P` need not be realised by
  any configuration; on such points `V(U(Δ))` is a formal SOCP value. That is the safe
  direction for a lower bound, but it must not be read as "every `Δ ∈ P` is a cover".
* `P` is compact and 8-dimensional; the anchor tuple `U(Δ)` depends smoothly on `Δ`
  in the interior, so `V` is continuous on `P` by the duality/boundedness argument.
  **Caveat (not a gap, but worth stating):** `V(U(Δ))` is only used where the
  functional is finite, which holds everywhere on `P` (Slater + connectedness).
* **Essentiality does not remove a `Δ = 0` boundary** because `P` has none. Correct.

---

## 4. Itemised verdict (conditional-relative-to-upstream, local, open)

Every row is relative to the listed upstream inputs; **no row is "unconditional" in
the sense of the whole chain being audited**. "interface-level" means: no hidden
premise found *inside* the interface, given the 9+2 canonical form and the fixed
graph of the class under consideration.

| # | Item | Status / dependency |
|---|---|---|
| 1 | Oracle formulation, Slater, strong duality, `V` finite/continuous | interface-level; graph-dependent (see #7) |
| 2 | `V(U) ≤ r` for every true cover (51 constraints necessary) | interface-level; given the 9+2 canonical form (C450/C451/C464) |
| 3 | Oracle drops only relaxations (not "exactly", just superset relaxation) | interface-level |
| 4 | Short-arc width bound; `m>0`, `P ≠ ∅`; `P` is an outer domain | interface-level |
| 5 | Switch existence + cyclic order (C905) | **C-up**: C905 not re-audited (depends on C451/C464/C879) |
| 6 | Straight embedding, 11 faces, Jordan ⇒ tile, hubs inside (C908) | **C-up**: C801/C802/C908 not re-audited |
| 7 | Fixed graph `(6,7)` with the two central faces | **C-up**: C450/C451/C464, C818/C819, k3/k4 closure certificates |
| 8 | MEC form necessary for non-acute faces | interface-level |
| 9 | `V(U*) = R*`, site uniqueness at `U*` (C909) | **local** (proved-interval at one anchor tuple) |
| 10 | `V ≥ R*` near `U*` (C910) | **local** (existential neighbourhood, no size) |
| 11 | **`V(U(Δ)) ≥ R*` for EVERY `Δ ∈ P`** | **OPEN** — the entire remaining global obligation |
| 12 | `min_P V ≥ R*` is *sufficient* to exclude `r<R*` | verified in this audit (interface-level) |
| 13 | `min_P V ≥ R*` is *necessary* for this route | verified: `V(U*) = R*` (C909) so the minimum is `≤ R*` |
| 14 | Covering radius `R*` for `n=11` follows from #11 + C892 | **conditional on #11** and on the C892 candidate chain |
| 15 | `Δ`-parametrised certificate family (force-dual loads over `P`) | **OPEN suggestion**, see §6 |

---

## 5. Is `min_P V ≥ R*` "enough", or is there a hidden premise?

**Interface-level: sufficient, and I found no hidden premise inside the interface —
but every use is conditional on the declared upstream list above.** Specifically I
checked and rejected the following candidate gaps:

1. *"Converse needed: oracle feasible ⇒ true cover."* Not needed. The direction used
   is cover ⇒ `V ≤ r` (via witness necessity). The file states this and it is right.
2. *"Non-acute faces make the face constraints invalid."* Wrong: the face's Voronoi
   vertex is a witness, so the MEC-form constraint is necessary for obtuse faces too
   (`MEC < circumradius` there — an equality-form argument would be false).
3. *"Anchors `U` must be realisable by a configuration with the fixed graph."* Not
   needed: `V` is defined for every `U ∈ P` by an SOCP, and the bound is used
   one-way. (`P` is an outer domain, not a set of realisable width vectors.)
4. *"`V` might be discontinuous / the min not attained."* Both fine (§3.5).
5. *"The width domain is over- or under-restrictive."* `≤ L` is necessary, `≥ m` is
   derived, `ΣΔ = 2π` is exact. No gap.
6. *"The switch cycle might not be the Delaunay cycle."* C905 + the radical-line
   argument give genuine Voronoi adjacency for each adjacent pair; boundary switches
   have exactly two winning sites, so the dual cycle is the ring in arc order.
   (Declared upstream, not re-audited here.)

**One genuine scope remark.** (G) alone reproves the global lower bound *only* in the
canonical q0(6,7) class. The complement of that class is handled by *other* bearing
dependencies (C818 for q1, C819 for q0(4,9), k3 for q0(5,8), and the `r ≤ 3/8`
certificate). Those are separate obligations and are **not** part of (G); the lead's
§6 says this and it is consistent with what I read. If any of those deponents were to
fail, (G) would not repair it.

---

## 6. What I verified numerically / computationally (diagnostic only)

Not evidence, but re-checked the interface constants:

```
  L = 2 asin(19/50) = 0.779592592948521          m = 2π - 8L = 0.0464445635914175 > 0
  nonempty test: m ≤ 2π/9 = 0.698131700797732 ≤ L   (9m = 0.418001072322757 < 2π)
  19/50 = 0.38 < sin(π/8);  (19/50)^2 = 0.1444 < sin^2(π/8) = 0.146446609406726
  8L = 6.236740743588168 < 2π = 6.283185307179586   (essentiality: 8·2 asin r < 2π)
  graph: n=11 sites (m_int=2 interior, h=9 abstract boundary) ⇒ F = 2·m_int+h-2 = 11,
         E = 3n-3-h = 21, Euler V-E+F = 11-21+11 = 1 (disk)
```

Also confirmed that the endpoint indexing is consistent with the cyclic ownership
(no equality between `r` and any constraint maximum is used anywhere in this audit).

**Scale of the open obligation (context, not a claim).** The candidate's bearings are
`b1 = 1.107`, `b2 = 1.0695` (from `hub_saturated_probe.json`), both `> 1`, so the
candidate sits in the high-bearing regime, while C860's witness has both bearings
`< 1`. The oracle graph `q0(6,7)` fans both cases, but the *additional* machinery
used to bound `V` is currently only valid for high bearings. A proof of #11 must
therefore either bound `V` for all bearings directly (the oracle itself is
bearing-free) or cover the low-bearing subregion by a separate argument — and by
Section 1, no bearing-restricted argument can substitute for the whole of `P`.

---

## 7. Files read for this audit

`lead/FIXED-SWITCH-SOC-REDUCTION.md`; `lead/FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md`;
`lead/CLIPPED-DUAL-STRAIGHT-EMBEDDING.md`; `lead/DUAL-DISK-INTERFACE-AUDIT.md`;
`lead/STRICT-EMPTY-FACET-COMPLETENESS.md`; `lead/LOCAL-CERTIFICATE-ASSEMBLY.md`;
`lead/Q0-CLOSURE-EXCLUSIONS.md`; `lead/HIGH-BEARING-BOUNDARY-THEOREM.md` (earlier
turn); `lead/interval_hub_boundary.py`, `lead/interval_cartesian_cancel.py`,
`lead/low_corner_jet.py` (independent context for the charts);
`lead/hub_saturated_probe.json`. Claims read in full via `claim_get`: C905, C908,
C909, C910.

**Not re-audited (declared dependencies, not premises I verified):** C450, C451,
C464 (9+2 canonical reduction), C818, C819, C820 and the k3/k4 closure dual
certificates, C892, C897, C902, C907.
