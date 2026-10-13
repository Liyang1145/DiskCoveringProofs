# n=14 object: order mapping + independent join — CONFIRMED

Scope: `research-2026/next-cover-global/members/candidate/`. All inputs read-only.
Reproduce: `py -3 -B members/candidate/n14_join.py` → `evidence/n14_join.json`, `evidence/join_run.log`.
**Numeric control only; no exact coverage claim.**

## 1. Sources and SHA-256

| role | path | sha256 |
|---|---|---|
| primary | `research-2026/session2/type14/out/hprec_sol.json` | `7689e60bdd2ecc8b54b589a3a30850e6a85040ca120c00bea225763753b9448a` |
| lead reference | `research-2026/next-cover-global/lead/n14-actual-vertices-numeric.json` | `4735772c63a9022ce8ca6fb25535e4d512706439763862e963a3757047660ea0` |

## 2. Correct object and order mapping

The candidate object is `th` (7 exact rationals), expanded **strictly** by
`research-2026/lead/verify_c407_lead.py` L185–195:

```
th = [F(s) for s in js['th']]
C = []
for j in (0,2):
    for s in (-1,1):
        for t in (-1,1):
            C.append((s*th[j], t*th[j+1]))      # indices 0..7 : two rectangles
for j in (4,5):
    C.extend([(th[j], F(0)), (-th[j], F(0))])   # indices 8..11: two x-pairs
C.extend([(F(0), th[6]), (F(0), -th[6])])       # indices 12..13: one y-pair
# len(C) == 14
```

**ORDER MAPPING (script index → file index)** — the file's `json['centers']` is in a
different order:

```
script→file permutation = [3, 2, 1, 0, 7, 6, 5, 4, 8, 9, 10, 11, 12, 13]
```

| script | file | coordinates (script order) |
|---|---|---|
| 0–3 | 3, 2, 1, 0 | `(±0.63509586304684604675, ±0.45425119231814842823)` (first rectangle) |
| 4–7 | 7, 6, 5, 4 | `(±0.29194111954460928155, ±0.84246738342778431480)` (second rectangle) |
| 8, 9 | 8, 9 | `(∓0.94337365737810986886, 0)` |
| 10, 11 | 10, 11 | `(±0.32681806871558222463, 0)` |
| 12, 13 | 12, 13 | `(0, ∓0.38861869814453937832)` |

The two rectangle blocks are the only ones reversed (both x and y sign order).
The inverse mapping is now **unambiguous and reversible**.

## 3. Why my earlier exact rational join failed

`json['centers']` stores **truncated** decimal floats, not the full literals:

| script idx | exact value (from `th`) | value in `json['centers']` | truncation |
|---|---|---|---|
| 0 | 0.63509586304684604674531547835 | 0.6350958630468461 | 5.3e-17 |
| 4 | -0.29194111954460928155316231103 | -0.2919411195446093 | 1.8e-17 |
| 8 | -0.943373657378109868862235539062 | -0.9433736573781099 | 3.1e-17 |
| 10 | 0.326818068715582224628395417639 | 0.3268180687155822 | 2.5e-17 |

Max residual over the tolerance join = **6.03e-17** (this *is* the truncation error).
An exact `Fraction` equality test therefore finds **nothing**; the join needs a tolerance
between the truncation (~6e-17) and the inter-centre separation (~0.48).

**My earlier `.32682` reading came from mixing the two orders** — for the three centres I
had labelled `{0,2,3}` (file order) the circumradius is 0.2739 (23× scale), and the
0.326818 that appeared was the norm of script-indices 10/11. Interface error, now closed.

## 4. Independent join of the vertex lists

I recomputed the nearest-site (Voronoi) vertices with circumcentre inside D from the
**exact `th` expansion** and joined against the lead's file:

| lead sites | my sites | \|Δq\| | lead radius | my radius |
|---|---|---|---|---|
| [0,6,13] | [0,6,13] | 1.14e-16 | 0.33173203427623404 | 0.3317320342762341235155 |
| [0,9,10] | [0,9,10] | 9.22e-17 | 0.33173203427623404 | 0.3317320342762341235155 |
| [0,10,13] | [0,10,13] | 8.37e-17 | 0.3317320342762341 | 0.3317320342762341235155 |
| [1,7,12] | [1,7,12] | 1.14e-16 | 0.33173203427623404 | 0.3317320342762341235155 |
| [1,9,10] | [1,9,10] | 9.22e-17 | 0.33173203427623404 | 0.3317320342762341235155 |
| [1,10,12] | [1,10,12] | 8.37e-17 | 0.3317320342762341 | 0.3317320342762341235155 |
| [2,4,13] | [2,4,13] | 1.14e-16 | 0.33173203427623404 | 0.3317320342762341235155 |
| [2,8,11] | [2,8,11] | 9.22e-17 | 0.33173203427623404 | 0.3317320342762341235155 |
| [2,11,13] | [2,11,13] | 8.37e-17 | 0.3317320342762341 | 0.3317320342762341235155 |
| [3,5,12] | [3,5,12] | 1.14e-16 | 0.33173203427623404 | 0.3317320342762341235155 |
| [3,8,11] | [3,8,11] | 9.22e-17 | 0.33173203427623404 | 0.3317320342762341235155 |
| [3,11,12] | [3,11,12] | 8.37e-17 | 0.3317320342762341 | 0.3317320342762341235155 |
| [4,6,13] | [4,6,13] | 1.42e-16 | 0.3208208548985308 | 0.3208208548985307637293 |
| [5,7,12] | [5,7,12] | 1.42e-16 | 0.3208208548985308 | 0.3208208548985307637293 |
| [10,11,12] | [10,11,12] | 3.48e-17 | 0.33173203427623416 | 0.3317320342762341235155 |
| [10,11,13] | [10,11,13] | 3.48e-17 | 0.33173203427623416 | 0.3317320342762341235155 |

**16/16 entries match by site triple; all q agree to < 1.5e-16.** The centre list also
joins index-for-index (residual ≤ 6.03e-17, the truncation floor).

Only **scale-level** differences remain, all attributable to the truncated file literals:
- lead's radii are quoted at ~17 significant digits; the exact expansion gives
  0.3317320342762341235155 for the 14 tight vertices and 0.3208208548985307637293 for the
  two slack ones (lead: 0.33173203427623404…416 and 0.3208208548985308).
- the two families separate at the 1e-17 level in the lead's file
  (0.33173203427623404 vs 0.33173203427623416); in the exact expansion both are
  0.3317320342762341235155, so that split is a truncation artefact, not geometric.

## 5. Status of the previously reported items

- **Withdrawn**: "n13/n15 have no symmetry" — the all-axis grid does not prove absence of
  symmetry, and the repeated norms in n13/n15 evidence near-reflection. Both are
  **unresolved**, not facts. n13/n15 profiling is **stopped** as not relevant to the choice.
- **Withdrawn**: my earlier n=14 "tight triple" lists and the "f−R ≈ −5e-17 is exactly tight"
  phrasing.
- **Confirmed and now usable**: the order mapping above, the exact `th` expansion, and the
  16 nearest-site Voronoi vertices with their site triples.
- D2 orbit structure: still to be re-derived in this authoritative indexing (my earlier
  statement of "7 orbits of 2" was the C2 orbit count; the full-D2 computation must be redone
  against these indices before use).

## 6. Next step (after this passes)

Resume exactification using **this** object: exact `th` expansion, the 16 vertices above,
and the 14 tight + 2 slack split. The low-dimensional system must be built on these triples
and indices, not on the withdrawn lists.
