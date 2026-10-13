# HUB-ADJACENCY-FINAL-AUDIT — the non-adjacency → nine-ring-two-circle argument

Assigned re-check of `lead/HUB-ADJACENCY-DUAL.md` (HAD), now that the C450 atom itself has
been source-audited (`C450-KERNEL-SCOPE-AUDIT.md`). Read line by line against HAD's own
text plus `lead/VORONOI-BOUNDARY-REDUCTION.md` (VBR), `C802`/`AUDIT-HUB-EDGE-BRIDGE-AND-Q-CLASSES.md`,
and `solo-20260922/M10-038-EXCLUSION.md` §1–§4. No kernel misreading repeated; the
hub-term question is not reopened. Only this file written.

**Verdict.** All six named steps are correct as written in HAD. Two of them are
*implicit but provable* and I make them explicit (§2 item 3 and the enlarged-hub
containment); my earlier version of this report added three errors of its own, which are
corrected below and marked as mine, not HAD's. No mathematical defect found in HAD.

---

## 1. Setup, and the constant `a`

HAD assumes `V_1 ∩ V_2` has no positive-length edge, so (`V_j` convex, `int`-disjoint)
the intersection is **empty or a single point** — this is C802's corrected hypothesis
`dim(V_1 ∩ V_2) ≤ 0`, not "empty interior" (which is automatic for distinct cells).

Write `h_j` for the hub sites, `e := |h_1|`, `R = 19/50`, and `r ≤ R` for the actual
radius. **The core radius must be `a := 1 − 2r`, not `1 − 2R`** — HAD writes
`U = B_open(0, a)` with `a = 1 − 2r`, and the ring-free property of the core uses that
same `r`. Fixing `a` at the value `a_R = 1 − 2R = 6/25` is *only* legitimate in the
final enlarged picture, where the three constants satisfy
`r + 2R − 1 = r − a_R`; in general

```
   U_R := B(0, a_R) = B(0, 1 − 2R)  ⟹  e ≤ r + 2R − 1 ≤ 3R − 1  at  r ≤ R .
```

Everything below uses `a = 1 − 2r` unless it says "enlarged".

***(Lead correction, recorded.)*** My previous version of this section defined
`a = 1 − 2R` and then derived `e ≤ 3r − 1` from it, which is not valid; HAD's own line
does the derivation with `a = 1 − 2r` and is correct. The error was mine, introduced in
the audit, and is fixed here. Two further errors of mine in the previous version are
corrected in §2 items (1) and (2), and one in the table of §3.

---

## 2. Step-by-step check of the six named items

**(1) `U ⊆ V_1 ∪ V_2`.** `U = B_open(0, a)` with `a = 1 − 2r`. For a ring centre `c` and
`|x| < a`: a boundary disk has centre norm `|c| ≥ 1 − r` (its disk meets `∂D`), so by the
triangle inequality

```
   |x − c|  ≥  |c| − |x|  >  (1 − r) − (1 − 2r)  =  r ,
```

so **x is covered by no ring disk**. *(Note the two steps separately: `|x| < a ≤ 1 − r`
alone gives only `|x − c| > 0`; the strict `> r` comes from comparing `|c| ≥ 1 − r` with
`|x| < 1 − 2r` and using `r > 0`. My earlier version wrote the chain as if
`|x| < a ≤ 1 − r ≤ |c|` already gave `> r`, which it does not; the conclusion is right,
the displayed chain was not.)* Since the configuration covers `D` and `x ∈ U ⊂ D`, `x`
lies in some disk of the configuration, and the only remaining disks are the two hubs;
being nearest to a hub is what `V_1 ∪ V_2` means. `U ⊆ V_1 ∪ V_2` ✔. *(Also `U ⊆ D`, so
the argument never leaves the target disk.)*

**(2) A point contact does not disconnect `U`.** If `V_1 ∩ V_2` is empty the argument is
immediate, so take the single-point case `V_1 ∩ V_2 = {p}`. The two sets

```
   (U ∩ V_1) \ {p}    and    (U ∩ V_2) \ {p}
```

partition `U \ {p}`, and each is **relatively closed in `U \ {p}`**, because it equals
`(U ∩ V_i) ∩ (U \ {p})` with `U ∩ V_i` relatively closed in `U`. **`U \ {p}` is
path-connected:** for `x, y ∈ U \ {p}`,

* if the segment `[x,y]` does not contain `p`, that segment is already a path in
  `U \ {p}`;
* if `p ∈ [x,y]`, choose `z ∈ U` not on the line `xy` (the line meets the open disk `U`
  in a set with no interior, so such `z` exists). `U` is convex, so `[x,z] ⊆ U` and
  `[z,y] ⊆ U`; and `p ∉ [x,z]` because `[x,z]` meets the line `xy` only at the point `x`,
  whereas `p ∈ [x,y]` and `p ≠ x`; the same argument gives `p ∉ [z,y]`. Hence
  `[x,z] ∪ [z,y]` is a path in `U \ {p}` joining `x` to `y`.

*(Equivalently, choose `z ∈ U` avoiding both lines `xp` and `yp`; then neither segment
can contain `p`.)* A connected set cannot be the union of two disjoint nonempty
relatively closed pieces, so one piece is empty: `U` lies in one cell. WLOG `U ⊆ V_1` ✔.

**(3) `e ≤ 3r − 1`: the containment `U ⊆ V_1` really does force it — with the enlarged
hub in place.** Taking closures, `B(0,a) ⊆ V_1 ⊆ B(h_1, r)`; the farthest core point from
`h_1` is the one on the opposite ray at distance `a`, so `e + a ≤ r`, i.e.
`e ≤ r − (1 − 2r) = 3r − 1 ≤ 3R − 1 = 7/50` ✔.

*The enlarged version, which the final contradiction needs, is a separate step and it
holds:* the original ball `B(h_1, r)` is a disk of radius `r` contained in the bounded
set `D`, so its centre satisfies `|h_1| + r < 1`. Taking `R = 19/50 > 1/3` and using
`3R − 1 = 0.14` gives

```
   |h_1| + R  ≤  (3R − 1) + R  =  4R − 1  =  0.52  <  1 ,
```

so `B(h_1, R) ⊆ B(0,1) = D`. Therefore the enlarged hub disk `B(h_1, R)`, enlarged from
the genuine compact cell `V_1 ⊆ B(h_1, r)`, still lies inside `D`; and since
`e + a ≤ r ≤ R` (at `r = R`, `e = 7/50` gives `a + e = 0.24 + 0.14 = 0.38 = R`) the
containment `B(0,a) ⊆ B(h_1,R)` continues to hold after enlargement. This is exactly the
containment the C450 reduction uses when it grows every centre-based disk.

**(4) After removing the redundant hub constraint, every ray exit carries a *ring*
facet.** Fix a unit direction `u` and let `h_1 + t u` (`t > 0`) be the first exit of the
ray from `V_1` along that direction. `h_1` is strictly interior to `V_1` — it is the site
of its own cell and that cell has nonempty interior (VBR §3) — so the ray meets `∂V_1`
for the first time at some `t > 0`, and `h_1 + t u ∈ ∂V_1`. *(The exit point is on the
boundary by definition, for every `t`; the earlier sentence in my version saying the
point is "strictly interior when `t < r`" is wrong and is deleted. What is true and
needed is only `t ≤ r`, from `V_1 ⊆ B(h_1, r)`.)* `∂V_1` is covered by finitely many
facet bisectors, so at least one constraint is **active** there:
`|h_1 + tu − x*| = |h_1 + tu − h_1|` for some site `x* ≠ h_1`. The other hub is excluded
as the *only* such site — if `x* = h_2` were active alone the point would lie in the
relative interior of the bisector segment `V_1 ∩ V_2`, contradicting `dim ≤ 0`. Hence
**a ring site is active**, and at a higher-order primal vertex the tie
`|h_1 + tu − c| = |h_1 + tu − h_1|` still holds for each of the tied ring sites, so
picking one gives the bisector equality

```
   |c − h_1|²  =  2 t u·(c − h_1) .
```

✔ *(This is HAD's "Radial facet lemma"; the only subtlety, that a vertex is admissible,
is handled because the identity is a tie-equality, not a two-site-only statement.)*

**(5) `t ≤ r ≤ R` ⟹ the radius-`R` disk covers `h_1 + R u`.** Substituting the identity:

```
   |h_1 + R u − c|² − R²  =  |c − h_1|² − 2R u·(c − h_1)
                          =  |c − h_1|² (1 − R/t)  ≤  0     because t ≤ r ≤ R ,
```

so `|h_1 + Ru − c| ≤ R` for the *same* ring site `c` ✔. Using `|c − h_1|²` is legitimate
even though the square contains `u·(c − h_1)` linearly: the product
`2t · u·(c−h_1) = |c−h_1|²` is the *value* of the identity, so `t` cancels exactly, and
the sign of the resulting `(1 − R/t)` is determined by `t ≤ R` alone. Since `u` was
arbitrary, the nine ring disks **enlarged to radius R with unchanged centres** cover the
whole circle `S(h_1,R)` ✔.

**(6) After enlargement the ring disks still meet `S¹`.** Enlargement keeps touching
disks touching: each ring disk met `∂D` at radius `r` and still does at radius `R`. So
each has a nonempty arc on `S(0,1)` ✔. *(HAD states this; it follows from enlargement
being monotone in the radius.)*

---

## 3. The exact C450 domain the HAD configuration must lie in — and does

The C450 atom is quantified over (M10 §1–§3): radius **`R = 19/50`** exactly, disks
**meeting `S(0,1)`**, `e ∈ [0, 7/50]`, **both radial roots**, all half-widths and
azimuths; each admissible single disk satisfies `Q < B/10`, while *coverage* of the two
circles by nine disks forces `ΣQ ≥ B`.

| C450 requirement | HAD configuration | check |
|---|---|---|
| common radius `R` | enlarged from `r ≤ R` | §2 item 5; enlargement is §1's own reduction |
| disk meets `S(0,1)` | **the nine ring disks**: they touch `∂D` by the arc structure and enlargement preserves touching | §2 item 6; `a > 0`. *(The hub disk is not part of this requirement and needs no such check — the atom's per-disk bound is applied only to the nine ring disks.)* |
| centre norm in `[1−R, 1+R] = [0.62, 1.38]` | **the nine ring disks**: after **C464's inward-root replacement** their centres satisfy `\|c_i\| ≤ sqrt(1−r²) < 1` and `\|c_i\| ≥ 1−r ≥ 1−R`; `1 < 1+R` | ✔ |
| **`e ∈ [0, 7/50]`** | `e ≤ 3r − 1 ≤ 3R − 1 = 7/50` (with the core radius `a = 1 − 2r`) | §2 item 3 **(the hub-side bound; this is the one HAD earns from non-adjacency, and it is the bound that puts the configuration into the certificate's `e`-range)** |
| both radial roots | the ring centres are **not** assumed to sit on the inner-root circle `\|c\| = sqrt(1−r²)`; the certificate keeps the outer root precisely because a radius-`R` disk meeting `S(0,1)` may have its centre anywhere in `[1−R, 1+R]` | ✔ (this is why the atom audit keeps the outer root) |
| both `S(0,1)` and `S(h_1,R)` covered by the nine | `S(0,1)`: the nine arcs cover `∂D`, and enlargement only adds; `S(h_1,R)`: §2 item 5 | ✔ |
| the hub is genuinely interior | `\|h_1\| + r < 1` (C451) | ✔ |

Then the sum step is literally HAD's: nine admissible disks covering both circles give
`Σ_{i≤9} Q(c_i;e) ≥ B(e)`, while the per-disk bound gives `Σ < 9B(e)/10` — contradiction.
**The contradiction uses only the per-disk inequality of the atom, plus coverage of the
two circles, plus `e ≤ 7/50`; all three are established above inside the quantified
domain.**

---

## 4. Remaining caveats (not defects)

1. **`e < 1 − R` vs. `e ≤ 3R − 1`.** Both are true; only the second is used, and it is
   the one that puts the configuration into the certificate's `[0, 7/50]`. Anyone
   re-reading HAD should not substitute the weaker boundedness bound.
2. **`t > 0`.** The facet identity divides by `t`; `h_1` is strictly interior to `V_1`
   (`h_1` is its own cell's site and that cell has nonempty interior, VBR §3), so the
   first exit is at `t > 0`. A degenerate `t = 0` cannot occur.
3. **Point contact vs. positive-length edge.** HAD's hypothesis is `dim(V_1 ∩ V_2) ≤ 0`
   (C802's corrected form). The conclusion is a positive-length edge. The empty case is
   covered by §2 item 2 (no puncture to route around).
4. **Degeneracies elsewhere.** HAD explicitly allows degree-`>3` vertices and does not
   assert trivalence or exclude skip-one chords; nothing in this audit needs those.
5. **Registered non-claims inherited.** HAD's own scope line: "new analytic reduction
   pending independent review, conditional on the existing C450 fixed-R dual
   certificate"; it does not enter the C801/C802 `d = 1`-implies-`K = k_1+k_2`
   bookkeeping beyond the statement that the hub edge exists, nor any radius bound.

**Errors of mine that this revision corrects (lead's review of the previous version; none
of them is a defect of HAD, and HAD's own text is correct on every one of these points):**

1. §1 previously fixed `a = 1 − 2R` and still derived `e ≤ 3r − 1`. The core radius is
   `a = 1 − 2r`, which is what makes that bound valid; the constant `a_R = 1 − 2R`
   belongs only to the enlarged picture and yields `e ≤ r + 2R − 1 ≤ 3R − 1`.
2. §2 item (1) previously displayed a chain of inequalities that would give only
   `|x − c| > 0`; the strict `> r` requires subtracting `|x| < 1 − 2r` from
   `|c| ≥ 1 − r` and using `r > 0`, which the corrected text now does explicitly.
3. §2 item (2) previously routed the connecting path through a boundary point of `U`,
   which is not in the open set; it is replaced by the corrected construction above
   (direct segment if it misses `p`, otherwise two segments through a point of `U`
   off the line `xy`), and the relatively closed pieces are now written
   `(U ∩ V_i) \ {p}` inside the punctured set `U \ {p}`.
4. §2 item (4) previously asserted the exit point is interior for small `t`; the exit is
   on `∂V_1` by definition, and that assertion is deleted.
5. §3's table previously listed the hub disk under the requirement "disk meets `S(0,1)`";
   the atom's per-disk requirement applies to the nine ring disks only, and the hub
   phrase is removed.
6. §2 item (3) previously carried an unclear clause about a bounded ball around a ring
   centre; it is deleted.

No claim registered; no subagent; no lead file modified.
