# R22 audit — norm-feasible A-interval formula (own scope, no claim)

Read-only, no lead file changes, no claim registered. Sources: the lead's stated formula,
`lead/face_totalangle_jet.py` (`legal`, `objective`), `lead/FACE-COMPLEMENT-REPRESENTATION.md`.

## Corrections applied after lead review (this section supersedes the text below)

Four sentences in the first version of this report were wrong and are **withdrawn**:

1. **Cap statement.** The lead's text is a conditional — "`T < pi/2` implies `A <= T/2`;
   `T > pi/2` implies `A >= T/2`" — not a claim that `T < pi/2`. My §6 read it as an assertion
   about the domain and is **withdrawn**; the identity behind it is a valid implication.
2. **"Identity verified by numeric NOT exact proof."** Correct: the reduction of `G` to
   `1 − s sin2b − d sin(2A+gamma)` is an *exact* algebraic identity obtained by expanding
   `cos 2(b+A)` and collecting `sin2b`, `sin2A`, `cos2A`. The numeric agreement was only a
   sanity check. My §2 wording is **withdrawn**.
3. **Sine period in `A` is `pi`, not `pi/2`.** `sin(2A+gamma)` has period `pi` in `A`; I wrote
   `pi/2`. **Withdrawn.** The single-band conclusion is nevertheless correct, and the lead's
   argument is the exact one: `|gamma| < pi/2` and `0 < A < T <= 2` give
   `-pi/2 < 2A+gamma < 2T + pi/2 <= 4 + pi/2 < 2pi`, so `sin >= sin(theta)` forces
   `2A+gamma in [theta, pi−theta]` — one band, no case split, and no appeal to a "second band".
4. **`a+ >= T` does not mean the whole wedge is feasible.** The feasible set is `[a−, T]` when
   `a+ >= T`, and `a− > 0` makes that a proper subinterval. My §5 sentence is **withdrawn**.
   What remains true and usable: the **upper endpoint `a+` needs the `min(T, a+)` clip**, which
   is exactly what the formula does.

---

## Verdict

**The interval formula is CORRECT. No counterexample.** One genuine side-condition must be
enforced, and one apparent domain inconsistency should be resolved in the text.

## 1. The two forms of `G` are identical

The lead's `G = 1 − s sin2b − (s − r sin2b) sin2A − r cos2b cos2A` and the form in
`face_totalangle_jet.legal` (`1 − s(sin2b + sin2A) − r cos2(b+A)`) agree to `3.9e-16` over 2000
legal points: expanding `cos 2(b+A)` gives exactly `s sin2b + r cos2b cos2A − r sin2b sin2A`.

## 2. Exact reduction to one sine inequality

```
u = s − r sin2b ,  v = r cos2b ,  c = 1 − s sin2b ,  d = hypot(u,v) ,  gamma = atan2(v,u)
G = 1 − s sin2b − [ s sin2A + r cos2b cos2A − r sin2b sin2A ]
  = 1 − s sin2b − ( u sin2A + v cos2A )
  = 1 − s sin2b − d sin(2A + gamma)                      (verified to 4.4e-16)
```

So `G ≤ 0 ⟺ d sin(2A+γ) ≥ c`. With `c > 0`, `d > |c|` (both below), the feasible set is the
preimage of `sin ≥ c/d = sin θ`:

```
2A + gamma in [theta, pi − theta]  (mod 2pi)
A in [ (theta−gamma)/2 , (pi−theta−gamma)/2 ]  (mod pi)
```

which is exactly the lead's `[a−, a+]` **[the "second band at +pi/2" is WITHDRAWN — the period in A is pi, and the lead's exact range argument shows theta-branch only]**. This is the branch-coverage argument: **one** sine branch, **one** band,
**one** interval — no case split is needed. The lead's phrasing with `cos` describes the same band
under the equivalent shift; the tested endpoints are the same.

## 3. Numerical set-equality check

Over 1500 random legal `(r, b, T)` with `b2 = T − b`,
`{A ∈ (0,T) : G ≤ 0}` equals `[max(0,a−), min(T,a+)]` with **0 mismatches** (dense A sampling,
tolerance `T/3000`). Earlier 154-point run also 0 mismatches.

## 4. Sign and factor claims — verified independently

| claim | status |
|---|---|
| `u = s − r sin2b > 0` | ✔ min `u = 0.5450` over `r∈[.379,.37999]`, `b∈[L,1]` |
| `c = 1 − s sin2b > 0` | ✔ min `c = 0.0746` |
| `d² − c² = s sin2b[2(1−r) − s sin2b] > 0` | ✔ identity holds exactly at 2000 sample points; min value `0.2914` |
| `theta = atan2(c, √(d²−c²)) ∈ (0, π/2)` | ✔ observed `theta ∈ [0.1370, 0.2673]`; branch is the safe one since both arguments are positive |
| `gamma = atan2(v,u)` open branch | ✔ `v = r cos2b` changes sign at `2b = π/2`; observed `gamma ∈ [−0.266, +0.226]`, so `atan2` (not `acos`) is required — as coded |
| `H = 2r sin(b+A) > 0` | ✔ implied by `0 < A < T ≤ 2` and `b + A < π`; no extra restriction in the formula |

## 5. One side-condition the certificate must carry

`a+ < T` is **not** automatic. Over 3000 random legal triples, `max(a+ − T) = +0.1233`, i.e. there
are legal `(r,b,T)` with `a+ > T`. **[WITHDRAWN: that does not imply the whole wedge is feasible — the set is `[a−,T]` and `a− > 0` makes it proper]** — but **when `a+ ≥ T` there is
no band at all to intersect**, and if a certificate branch expects an interior band it will be
empty for that triple. Recommend stating: `T > a+` is the condition under which the norm boundary
actually cuts the arc; otherwise the arc is entirely inside the norm disk.

## 6. Cap statement — WITHDRAWN (see corrections)

The request states `T ∈ [2L, 2]` **and** "opposite-face cap ⇒ `T < π/2`, `A ≤ T/2`". **[WITHDRAWN]** As originally read by me this looked inconsistent: `2L = 1.21892 > π/2 = 1.5708`? No — `2L = 1.2189 < π/2 = 1.5708`, so `T ∈ [1.2189, 2]`
straddles `π/2`. The two statements are consistent only if the cap constraint `T < π/2` is an
*additional necessary condition* that further restricts the domain to `T ∈ [2L, 2] ∩ (0, π/2]`,
i.e. `T ∈ [2L, π/2]`. If instead `T` is allowed up to 2 (as written), then the cap `A ≤ T/2`
must not be imposed — my checks show the interval formula is valid for all `T ∈ [2L, 2]` and the
exact feasible set is always contained in `(0,T)`.

The statement is in fact a conditional implication, so there is nothing to resolve. Also worth recording: `T ≤ 2b` is *not* needed for the band to lie in `(0,T)`; it held
automatically in every sampled case (`a+ < T` whenever a band exists).

## 7. Repro

```
cd research-2026/team-current/cline2-closure-kernel
py -3 r22_clean.py           # identity, band derivation, 1500-point set equality, side conditions
py -3 r22_norm_interval.py   # earlier 154-point set equality + sign/factor checks
```
