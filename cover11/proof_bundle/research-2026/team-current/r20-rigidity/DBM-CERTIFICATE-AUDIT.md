# DBM cosine-polytope: independent kernel audit (r20-rigidity)

Artifacts audited: `lead/cosine_polytope.py` (DBM cells on `t0=0, t9=1`, `t_j-t_i = sum y[i:j]`),
`lead/certify_cosine_polytope.py` (interval minorants + exact-rational residual dual),
`lead/reflect_energy_fields.py` (exact graph permutation). Independent instrument: `dbm_audit.py`
(this directory, no lead helper import, exact Fractions). Not audited: the old simplex tree, and any
global conclusion (tree source `cosine_dbm_near.json` retains all open leaves).

## Items checked analytically

1. **DBM domain and signs.** `db[i][j]` upper-bounds `t_j - t_i`; with `y >= 0`, `sum y = 1` one has
   `t_i - t_j <= 0` for `i < j`, hence the root table `db[i][j] = 0 (i=j)`, `1 (j>i)`, `db[9][0] = -1`
   (`t_0 - t_9 = -1`). `closure` is exact Fraction Floyd-Warshall and rejects a negative diagonal.
   `domain_rows` emits, for each `i<j`, the row `1_{i<=k<j}` with `b = db[i][j]` **and** its negation
   with `b = db[j][i]`: since `(t_i - t_j) = -sum y[i:j]`, `A y <= b` is the correct orientation in
   both directions. **90 rows**, including every pair touching node 9. Checked exact: prefix identity
   `t_j - t_i = sum y[i:j]` and `A y <= b` for 20 rational simplex points.
2. **Residual dual direction.** For `A y <= b`, `lambda >= 0`, `y >= 0`, `sum y = 1`:
   `f0 + c.y >= f0 + c.y + lambda.(A y - b) = f0 - lambda.b + (c + A^T lambda).y
   >= f0 - lambda.b + min_i (c + A^T lambda)_i`. The code's `lb` implements exactly the right-hand
   side, and it is **re-evaluated outward** (line 27-28 recomputes `f0 - sum lam*b` inside the interval
   sum and then adds the *lower* bound of the residual minimum), so no rounded `mp` addition is used
   as a bearing endpoint. Checked exact on random rational `lambda >= 0`, `y` in the domain.
3. **Trigonometric arc signs.** For a pair `(i,j)` the code uses
   `aa = (i-j)L + D(-db[j][i])`, `bb = (i-j)L + D db[i][j]`, then `a = lo(aa)`, `b = hi(bb)`; this is
   the outward envelope of `z = theta_i - theta_j = (i-j)L + D sum y[i:j]` because
   `sum y[i:j] in [-db[j][i], db[i][j]]`. The minorant used is `certify_cosine_envelope_cell.intercept`,
   whose critical-point enumeration carries the coverage guard `a > -2pi`, `b < 2pi` (an assert), so a
   too-wide arc fails loudly rather than silently.
4. **LP numbers propose only.** `beta`, `gamma` and `lam` are rationals produced by `normalize` /
   rounding of LP duals and then hard-asserted (`sum == 1`, `min >= 0`, `len(lam) == len(A)`); nothing in
   the certificate uses LP optimality, feasibility status or multiplier signs.
5. **Reflect permutation (exact).** `p(i) = (4-i) mod 9` on sites, `fp` the induced face map (checked a
   bijection of the 11 faces), `node(i) = (3-i) mod 9` on anchors, `p` on sites, `fp` on auxiliaries;
   the induced edge permutation is a bijection and an **involution** of `{0..50}`, `alpha` is permuted
   and re-asserted as a positive probability vector, and the 36 reflected weights are re-indexed. I
   additionally verified the *anchor/site consistency*: for the edge `(9+s, s)` the image is
   `(9+p(s), (3-s) mod 9) = (9+p(s), p(s)-1)` and for `(9+s, (s-1) mod 9)` it is `(9+p(s), p(s))`, i.e.
   both are again anchor-site edges; the shift by 1 between the site map and the anchor map is exactly
   what preserves the edges. All exact, no numeric field approximation.

## Findings

* No error found in the audited items. In particular the two things most likely to be wrong are right:
  the `domain_rows` orientation (both directions present, correct `db[i][j]`/`db[j][i]` pairing) and the
  sign/direction of the residual dual (`- lambda.b` with `+ min(c + A^T lambda)`).
* Scope notes (not errors): the *geometric* reading of the anchor map as "reflection about the axis
  through anchors 2-3 bound" is a modelling premise; the code asserts the graph-level facts only. The
  tree remains all-open (`cosine_dbm_near.json`, 75 open), so no global conclusion is implied and none
  is claimed here. `intercept`'s guard `(a,b) in (-2pi, 2pi)` is load-bearing for wide DBMs.

## Reproduction

`py -3 -B -X utf8 dbm_audit.py` -> `dbm_audit.json/.log` (exact-Fraction controls D1-D4 above).
No new claim; no LP re-run.
