# AUDIT A/B result — source ids, coordinate localisation, and the two label bugs

Read-only audit requested by the lead. No optimisation, no new claims. Full raw log:
`out/audit_A_B.txt` (tool: `tools/audit_A_B.py`, run from repo root).

## Sources (exact)
* `n11/upper/certified_object.json` — `centers_scaled_1e17`; row 0 = hub A `(-0.000162043,-0.149428411)`,
  row 2 = hub B `(0.000296021,+0.272977306)`.
* `research-2026/team-current/lead/check_r20_chain_variance.py` (weights/points, `r=0.3799838531198388`)
* `research-2026/team-current/lead/R20-CHAIN-HUB-CONVEXIFICATION.md` (hypotheses)
* `research-2026/team-current/lead/check_r20_chain_hub_sets.py` (pin/active calibration)
* my counterexample: `C883` / `tools/outer_corrected.py` unit
  `a=(-0.23763005,-0.58241778)`, `b=(0.48422478,-0.42854144)`, `r=0.37998385311983873`.

---

## AUDIT A — the C883 pair fails the convexification's interface hypothesis (claim corrected)

Computed on the C883 pair (`a = c_i`, `b = c_j`), `m=(a+b)/2`, `n = J(b-a)/d`, `A=d/2`, `k=sqrt(r²-A²)`:

| hypothesis (R20-CHAIN-HUB-CONVEXIFICATION.md) | value on the C883 pair | holds? |
|---|---|---|
| H1: the two disks' **actual covered unit-circle arcs meet in exactly one equal-distance point U** | covered arc of `B(a,r)`: angular span `0.207562`, of `B(b,r)`: `0.347863`; **intersection length `0.000000`** | **NO** |
| H1': `U = m + t₊ n` (the `t₊>0` unit-circle point on the radical line) is covered by both disks | `U = (-0.19359009, +0.98108250)`, `|U-a| = |U-b| = 1.564120409 > r`; not in either covered arc | **NO** |
| H2 (Lemma 1): `A² + t₊² ≤ r²`, i.e. `t₊ ≤ k` | `A²+t₊² = 2.446472655` vs `r² = 0.144387729`; `t₊ = 1.519962030` vs `k = 0.090551906` | **NO** |
| H3 (Lemma 1): `A² + t₋² > r²`, i.e. `t₋ < −k` | `A²+t₋² = 0.366402650 > r²`; `t₋ = −0.479806804 < −k = −0.090551906` | yes (vacuous) |
| H4 (Lemma 1): `p_out = m + k n` outside int D, `p_in = m − k n` strictly inside | `|m+kn| = 0.429794702 < 1`, `|m−kn| = 0.610818764 < 1` | **NO** |
| H5: hubs strictly interior | C883 hub `|h| = 0.429794702 < 1−r = 0.620016147` | yes |

**Correction of my C883 "nonconvex" claim.** On the C883 pair the two disks' covered unit-circle arcs are
disjoint; there is no common covered equal-distance point `U`, so the pair **is not a legal ring
interface** in the sense required by the convexification. My sentence "the chain hub domain is
`⋂(B(p_k^in,R) \ B(p_k^out,R))` — not convex" was derived from a pair outside that domain and must
be **withdrawn as a statement about the convexification's domain**. What survives, stated correctly:

> for an arbitrary annulus pair with `|c_i|,|c_j| ≥ 1−r` and `d ≤ 2r` the interface hypothesis
> (unique common covered tie `U`) is **not automatic**; when it fails, `|p_out| < 1` is possible
> and the outer constraint is not redundant.

The **domain-internal** statement (with H1 holding) is the honest test, and I have verified it
numerically on the *actual* chain of the certified object: for every one of the 9 chain edges the
inner pin satisfies `|H − p_in| = r` exactly, i.e. `rho(c_i,c_j,H) = r ≤ r` with equality, and the
outer roots all have `|H − p_out| ≥ 0.542 ≫ r`. So the convexification is correct on the realised
chain; my counterexample simply is not in its domain. **No correction to the lead's theorem is
needed**; the correction is to my claim.

---

## AUDIT B — the pin labels: two distinct bugs, both localised

### B1. The lead's variance calibration is consistent, but the hub it reproduces is **H_A**, not H_B.
Running `check_r20_chain_variance.py` from the repo root (it needs cwd = repo root; it also
overwrites `lead/r20_chain_variance.json`) gives
```
edge_indices = [4, 6, 8]
points =
  (-0.37866873651434624, -0.11595586133734863)
  (-0.0005741023530978287, -0.5294120407837313)
  ( 0.37841635673703006, -0.11677685837533505)
weights = (0.45997773056271785, 0.08004453927415564, 0.45997773016312643)
r = 0.3799838531198388
```
Independent identification of those three points inside my own pin list (min-norm roots of the
node-edges `(i,i+1)` in the same `c[]` ordering, hubs at `c[9]=H_A`, `c[10]=H_B`):

| lead point | = my min-norm pin of node-edge | `|H_A − ·|` | `|H_B − ·|` |
|---|---|---|---|
| `(-0.37866874, -0.11595586)` | `(8,0)` | `0.379983853120` | `0.543031579401` |
| `(-0.00057410, -0.52941204)` | `(1,2)` | `0.379983853120` | `0.802389818423` |
| `( 0.37841636, -0.11677686)` | `(3,4)` | `0.379983853120` | `0.543031579728` |

So the lead's three pins **are my node-edges `{1,3,8}` as a set**, and:
* `weights · pins = (-0.00016204, -0.14942841) = H_A` (`|diff| = 6.83e-18`);
  `H_B` is off by `0.422406`;
* `|H_A − pin| = r` for all three (machine precision), so the C879 identity holds with
  variance `− r² = −1.94e-16`;
* `|H_B − pin| = 0.543031579 / 0.802389818 / 0.543031580` — none equals `r`.
The script's variable is `h = c[10]`, which reads as hub B. **Label bug (lead's script), not a
mathematical error**; the calibration itself is correct and tight, for hub A.

### B2. My "H_B is outside the pin triangle" was also wrong, because I used the wrong three pins.
* The pins whose distance to **H_B** equals `r` are node-edges **{4,5,6,7}** (margins
  `-2.2e-16, -5.6e-16, -3.9e-16, -2.2e-16`), i.e. the 4-edge chain of H_B.
* The pins whose distance to **H_A** equals `r` are node-edges **{1,3,8}** (margins
  `-1.7e-16, -1.7e-16, -2.8e-16`), i.e. the 3-edge chain of H_A.
* For the lead's pins `[4,6,8]` and the **correct hub**: independent linear solve of
  `[[1,1,1],[p_x],[p_y]]·λ = (1, H_A)` gives
  ```
  λ = (0.459977730563, 0.080044539274, 0.459977730163)     all > 0  → H_A is INSIDE the triangle
  ```
  whereas the same solve with `H_B` gives
  ```
  λ = (0.971308237805, -0.942616479697, 0.971308241892)    one λ < 0 → H_B is OUTSIDE
  ```
  (my earlier statement `[1.1195,−1.0226,0.9031]` was obtained in my own ring order, not the lead's;
  the sign conclusion agrees with the lead's coefficient, the numbers differ by the map).
* Reason the lead's three pins `[4,6,8]` are "active" for **H_A**: node-edges 4 and 8 lie one step
  outside the pins `{1,3,8}`; all four points are on the circle of radius `r` about H_A.
  Verified `|H_A − pin[4]| = |H_A − pin[6]| = |H_A − pin[8]| = r` to 1e-16.

**Corrected statement.** Both calibrations are consistent once the hub is identified:
* **hub A** (`c[9] = (-0.000162043,-0.149428411)`): active pins `{1,3,8}`, all at distance `r`
  (machine precision), their angles about `H_A` are `-90.06° / 4.93° / 174.95°`, and
  **`H_A` is inside their triangle** with `λ = (0.080044539, 0.459977730, 0.459977731)` —
  exactly the lead's weight triple, permuted. (`H_B` in the same triangle has
  `λ = (-0.94261648, 0.971308242, 0.971308238)`, one negative.)
* **hub B** (`c[10] = (0.000296021,+0.272977306)`): active pins `{4,5,6,7}`, all at distance `r`,
  angles about `H_B` = `4.93° / 54.55° / 125.33° / 174.95°`; their convex hull is the quadrilateral
  `(0.3789,0.3056),(0.2207,0.5825),(-0.2194,0.5830),(-0.3782,0.3065)` whose `max y = 0.58 > 0.27`
  and `min y = 0.3056 > 0.2730`, so **`H_B` is strictly BELOW the whole quadrilateral and hence
  outside its hull**. (`lstsq` weights `(0.5597,-0.0597,-0.0597,0.5597)`, one negative;
  the LP for `H_B ∈ conv{4,5,6,7}` is infeasible. Any three of them, e.g. `{4,5,6}` with pairwise
  distances `0.318878/0.659470/0.440132`, gives `λ = (1.119483,-1.022572,0.903089)` — the reading
  my earlier note quoted in my own ring order.)
So the C879 uniqueness mechanism (`h* ∈ conv{pins}`) **fires for hub A and not for hub B**; it is
not a chain-size effect. The lead's calibration is therefore a correct, tight C879 instance of hub A.

### B3. My own report's "|p_out| = 1 for all eight adjacent pairs" was a **label swap**.
`tools/arc_account.py` prints the exposed rim arcs as `(centre, halfwidth)`; the printed `halfwidth`
of ring `i` equals `arccos(|H − c_i|/(2R))`, which is the **distance-derived quantity**, while
`|p_out|` is a property of the *pair* (the second radius-r circle centre). I conflated the two in
the sentence "|p_out| = 1 … for all eight pairs". The claim C886 must be read only as:
**for all eight adjacent pairs `|p_in| ∈ [0.396, 0.623]` and the exposed-arc maxima equal `R`**;
the `|p_out| = 1` statement applies to the *pins of the candidate*, i.e. it is the statement
`|p_in| = |m − k n| < 1` vs the pair's other root, and must be re-derived before any use.

## Net effect
* The convexification (lead) survives Audit A; my C883 counterexample is out of its domain.
* Audit B resolves the pin-set dispute: `[4,6,8]` **are** active, for **H_A**, and `H_A` **is**
  inside their triangle; H_B's own active set is `{4,5,6,7}`. The conflict the lead flagged is a
  label/mapping bug on both sides, not a mathematical discrepancy.
* No new claims registered (as instructed).
