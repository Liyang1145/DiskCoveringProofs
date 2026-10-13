# ARC-LEDGER-SOURCE-AUDIT (r20-chain) — source reasoning of the arc ledger and the connected-ownership interface

Audit only (no new claim, `lead/` untouched, no subagents).  Sources located by glob, not guessed:
`research-2026/team-max-20260922/n11-structure/ARC-COORD.md` and
`research-2026/team-current/lead/VORONOI-BOUNDARY-REDUCTION.md`.  Dependency read:
`ARC-Q2-CHECK.md` (C1/C2/C3, independently reviewed per ARC-COORD's header) and the wedge lemma (N11S-2).

## 1. What the ledger proves, and from what

Ledger: arcs `I_i = [φ_i − t_i, φ_i + t_i]` (closed, half-width `0 < t_i ≤ arcsin r`), cyclic phases
(`γ_i = φ_{i+1} − φ_i > 0`), `o_i := t_i + t_{i+1} − γ_i`, `ℓ_i := 2t_i − o_{i−1} − o_i`.
`P2 = {0 < t_i ≤ arcsin r, o_i ≥ 0, Σo_i = 2Σt_i − 2π, ℓ_i > 0}` and the theorem is
`P1/(mod rotation) ≅ P2` with `γ_i = t_i + t_{i+1} − o_i`.

**Total-capacity link (the lead's question).**  The scalar ledger equation `Σ_i o_i = 2Σ_i t_i − 2π`
says exactly: *the summed excess of half-widths over π equals the total overlap.*  With `o_i ≥ 0` it
gives the **total capacity bound `Σ_i t_i ≥ π`**, and with the per-disk capacity `t_i ≤ arcsin r` it
gives `π ≤ Σt_i ≤ 9 arcsin r`.  So `o` is not an independent datum: it is the redistribution of the
capacity surplus, and `Σo_i` is pinned by the closure of the cycle.  (Numerically the cap side is not
binding — `9 arcsin(19/50) ≈ 3.508 > π` — the content is the *equality* and the sign of the surplus.)

**How the three claimed properties arise.**

* **neighbour-only overlap**: derived, not assumed.  `ARC-Q2-CHECK.md` C1/C3 (no inclusion; non-neighbour
  arcs disjoint) with the cyclic ordering show the only arcs overlapping `I_i` are `I_{i−1}, I_{i+1}`;
  independently, in the reverse direction S3 *re-derives* non-neighbour disjointness from the interior
  `ℓ`-conditions: summing `o_{j−1} + o_j < 2t_j` over interior `j` of a gap of length `k` yields
  `2Σ t_j ≥ Σ o_j`, i.e. `Σγ ≥ t_i + t_{i+k}` (uses `o ≥ 0`), so `I_i ∩ I_{i+k} = ∅`.
* **no triple overlap**: a consequence — any point in three arcs would put a non-neighbour pair in
  contact with a third arc at that point, contradicting non-neighbour disjointness; the ledger's
  `ℓ_i > 0` never needs a third arc.
* **9 actual arcs essential**: `I_i \ (I_{i−1} ∪ I_{i+1}) = (L_i + o_{i−1}, R_i − o_i)`, whose length is
  `ℓ_i` (using `R_{i−1} = L_i + o_{i−1}`, `L_{i+1} = R_i − o_i`); essentiality ⟺ that open interval is
  nonempty ⟺ **`ℓ_i > 0`**.  Conversely `ℓ_i > 0` forces `o_i < min(2t_i, 2t_{i+1})`, hence `γ_i > 0`
  (S1) — so the ledger's strict inequalities imply the geometry, not merely record it.

**Tangent / redundant / endpoints (checked against §4 of the source).**

| case | ledger handling | audit note |
|---|---|---|
| tangent `o_i = 0` | **allowed**, kept as an independent variable, closed inequality | the shared point is covered by both closed arcs, so coverage and the counts are unchanged |
| `ℓ_i = 0` (redundant) | **excluded** as violating essentiality; wording "private part empty / deletable", **not** "private single point" | correct: the degenerate point is already covered by the neighbours |
| endpoints | private part is the **open** interval; essentiality uses nonemptiness of an open interval | strictness of `ℓ > 0` is exactly what carries the endpoint bookkeeping |
| `t_i = arcsin r` (double root) | **allowed**, cannot be excluded; the retracted claim "absent for `r ≤ 0.38`" is **withdrawn** | consistent: `arcsin(19/50) ≈ 22.3327° < 22.5° = π/8` |
| generic | both `o > 0, ℓ > 0` | no WLOG normalisation |

Constraint trichotomy is explicit in the source: one **equality** (`Σo`), closed inequalities (`o ≥ 0`),
strict inequalities (`ℓ > 0`).  Dimension bookkeeping: ledger 17 (rotations already quotiented),
unquotiented configurations 18, and **no 16** (the `Σγ = 2π` identity is automatic, not an independent
constraint) — the source records the reviewer's own correction to the same effect.

## 2. Not the nearest-owned arc (the conflation the lead warned about)

The ledger's `I_i` is the **actual covered arc** `B(c_i, r) ∩ ∂D` (centre phase `φ_i`, half-width `t_i`),
with `t_i < arcsin r` corresponding to the **inner root** convention
(`ρ_i = cos t_i − √(r² − sin² t_i)`, equivalently `ρ_i ≤ √(1−r²)`; the two roots coincide at
`t_i = arcsin r`).  It is **not** the nearest-centre (Voronoi) arc.  Two different objects:

* `I_i` — where disk `i` covers the circle;
* the ownership arc — where centre `i` is the nearest centre, which `VORONOI-BOUNDARY-REDUCTION.md` §1
  shows is **one connected closed sub-arc of `I_i`**, of positive length.

Consequences of keeping them apart: `o_i` measures *covering* overlap, while the switch points `U_i`
(the ownership boundaries) lie inside the overlaps; the ledger's `t_i ≤ arcsin r` is a covering-capacity
bound and says nothing by itself about the ownership arcs, and the reverse direction S3 must therefore be
used when transferring ledger conclusions to the switch coordinates.  (The retracted polar-appendix
statement was of exactly this kind: `d_i ≥ 1 ⟺ o_i ≥ 0` needs C1; the undirected distance `d_i` must be
replaced by a **directed support** `max_i⟨w_i, u(θ)⟩ ≥ 1`.)

## 3. Connected ownership (from `VORONOI-BOUNDARY-REDUCTION.md` §1)

Argument as given there, condensed: outside `I_i` no point can be in disk `i`'s nearest-cell (some
covering centre has distance `≤ r` while centre `i` is farther than `r`); in the private open part of
`I_i` disk `i` is strictly closest; in an overlap `I_i ∩ I_{i+1}` only those two disks can win, and the
difference of squared distances restricts to a **nonconstant affine function on the circle**; at the
overlap's first endpoint disk `i` is strictly closer and at its last endpoint disk `i+1` is, with strict
inequalities because each actual arc has length `< π` and the endpoints are distinct; a line meets a
circle in at most two points and opposite endpoint signs force an odd number of transversal
intersections, hence **exactly one** intersection in the overlap (a tangent zero cannot change sign and
cannot coexist with a transverse zero); a zero-length overlap contributes its single common endpoint as
the unique tie.  Therefore each `I_i` contains exactly one connected closed nearest-centre boundary arc
of positive length, and there are **exactly nine distinct nearest-centre boundary switches**.  The two
interior disks own no boundary point at all: `|h| + r < 1` gives `|u − h| ≥ 1 − |h| > r` while some ring
disk covers `u`.

Cross-consistency with the fixed-switch oracle (checked, no claim added): the switches are the `U_i` of
`FIXED-SWITCH-SOC-REDUCTION.md` §1 and of the gluing code — `U_i` is the switch between ring `i` and
`i+1`, and ring `i` owns `[U_{i−1}, U_i]`.  This matches the gluing convention (`mk('end', i, U[i])`,
`mk('end', i, U[(i-1) % 9])`) that I verified earlier, i.e. the ownership statement and the oracle's
18 endpoint constraints describe the same intervals.

## 4. Audit findings (dependencies, corrections carried, scope)

* **Dependencies (not derivable inside `ARC-COORD.md` alone)**: C1/C2/C3 from `ARC-Q2-CHECK.md` (path
  prefix C2 gives adjacent overlap; C3 gives non-neighbour disjointness) and the wedge covering lemma
  (N11S-2) for S4.  The header records independent review of `ARC-Q2-CHECK.md` by `n11-hole` and
  `max-c450-review`; the ledger's own §5 appendix is explicitly **frozen/unreviewed** and not to be used.
* **Corrections already carried in the source** (so downstream must not re-use the old forms): the
  "`t = arcsin r` absent for `r ≤ 0.38`" claim is **retracted**; the `ℓ_i = 0` wording is corrected to
  "empty/deletable private part"; the polar edge condition must use **directed support**; the dimension
  bookkeeping is 17 (mod rotation) / 18 (with rotation), **no 16**.
* **Two-step logic to keep apart when reusing this for the fixed-switch obligation**: (i) ledger ⇒
  covering/essentiality structure on the *actual* arcs; (ii) §1 ⇒ ownership = one connected sub-arc per
  disk and nine distinct switches.  Step (ii) is what licenses fixing the switches `U`; the ledger alone
  does not.
* Scope of this audit: restatement, dependency tracing and cross-consistency only.  No new certificate,
  no numerical claim, no statement about the optimum `r_D(11)`.
