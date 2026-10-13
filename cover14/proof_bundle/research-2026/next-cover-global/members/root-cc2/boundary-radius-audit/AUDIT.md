# root-cc2 boundary-radius-audit: audit of the boundary-facet extension (corrected)

Scope `members/root-cc2/boundary-radius-audit/` (only). Lead artifacts read-only.
**No claim registered.** This file replaces my earlier draft; the statements listed in
section 6 are withdrawn. Lead proof unchanged. All checks below are symbolic
(`evidence/symbolic01.txt`).

## Verdict

The extension is correct. The boundary-edge interface supplies exactly the two inputs the
deficit lemma consumes, the length identities are exact, the per-face ledger is the real
face angle sum, and the packing/degeneracy bookkeeping is sound.

## 1. Boundary-edge interface (correct)

With `u=(0,0)`, `v=(l,0)`, `w=(w_x,w_y)`, `z=(l/2,h)`:

    |z-u|^2 - |z-w|^2 = 2 h w_y + l w_x - w_x^2 - w_y^2,

so the nearest-site condition for `u` is `h <= (w_x^2+w_y^2-l w_x)/(2 w_y) = h_f`; `h_f` is
the circumcentre ordinate. The proof assumes **only** `h_A <= h_f` (no sign hypothesis on
`h_A` or `h_f`): `phi_A = atan(2h_A/l) in (-pi/2, pi/2)` and
`gamma_A = pi/2 + phi_A in (0,pi)`. Then

    bearing(O_f - u) = pi/2 - gamma_f,  bearing(A - u) = phi_A,  beta = their difference,
    gamma_f + gamma_A = pi - beta,
    R_f sin gamma_f = l/2 = rho_A sin gamma_A

(the last two are the right-triangle identities at `O_f` and `A`). `h_f = 0` is the
**right-triangle** case `(u-w).(v-w) = w_x^2 - l w_x + w_y^2 = 0`, not a collinear
degeneracy, since `w_y > 0` throughout.

The paired facet area is `R_f rho_A sin beta`: with `O_f-u = (l/2,h_f)` and
`A-u = (l/2,h_A)`, `cross(O_f-u, A-u) = l(h_A-h_f)/2` (sympy), so
`sin beta = |cross|/(R_f rho_A)` and `R_f rho_A sin beta = (l/2)|h_f-h_A| = 2 area(u,O_f,A)`.
This is what the note states.

## 2. Per-face ledger (correct, and it needs only the face angle sum)

With `Delta_fe := gamma_fe - (pi-beta_e)/2` and `gamma_fe` the **real** opposite interior
angle of triangle `f`:

    sum_e Delta_fe = sum_e gamma_fe - (3pi - sum_e beta_e)/2,

and `sum_e gamma_fe = pi` gives **exactly** `sum_e Delta_fe = (sum_e beta_e - pi)/2`
(sympy: the difference is identically `0`). `gamma_fe` is the real angle for every edge,
the boundary edge included (taken at `O_f`), so `sum_e gamma_fe = pi` is the ordinary angle
sum of the real face. No second identity and no alternative convention is involved.

## 3. Lemma chain (correct; my inequality direction was wrong)

With `tau = |x-y|/(x+y)`, `M = max(x,y) <= 1`, `m = min(x,y)`:

    x y = M m = (m/M) M^2 <= m/M = (1-tau)/(1+tau),

because `M^2 <= 1`. Equivalently `1 - x y >= 1 - (1-tau)/(1+tau) = 2 tau/(1+tau) >= tau`
(sympy: `1-(1-tau)/(1+tau)-2tau/(1+tau) = 0`). Hence

    D_e = U^2(1-xy) sin beta >= U^2·2tau/(1+tau)·sin beta >= U^2 tau sin beta, and with
    `t = tan(beta/2)`, `sin beta = 2t/(1+t^2)`, `1-cos beta = 2t^2/(1+t^2)`,

    tau sin beta = |tan Delta| tan(beta/2) sin beta = |tan Delta|(1-cos beta),

so `D_e >= U^2(1-cos beta)|tan Delta| >= U^2(1-cos beta)|Delta|`. The boundary case uses
the identical chain with `rho_A` in place of `R_g`. (My earlier draft had the `xy`
inequality reversed and then, after the lead's first correction, reversed it again; the
direction used here is the lead's derivation `xy <= (1-tau)/(1+tau)` and is the one the
deficit chain requires.)

## 4. Packing, limits (correct)

A single face gives `U^2/2 · m_f |sum_e beta_e - pi|`. Summing over **all** faces counts
each interior edge twice → `U^2/4 · sum_f m_f |...|`; for an **edge-disjoint pack** no edge
is shared inside the pack, so the factor stays `U^2/2`. Fan-diagonals have `beta = 0` and
contribute nothing (and force `m_f = 0` for any face containing one). The compact-limit
argument (constant-graph subsequence in `eps`, then pass `r` to `U`) uses only continuity
of the deficit. Note: `rho_eps` may **exceed** `r` before the limit; the only endpoint
relation used is at the limit, `rho_A <= r <= U` — no `rho_eps <= U` claim is made at any
finite `eps`.

## 5. Certification status

The directed-interval suprema and the independent Fraction partitions for the 12 face packs
are **already completed** (all 12 negative), per the lead. That step is not a gap in this
extension; I do not audit the counts here.

## 6. Withdrawn from my previous draft

1. Invented hypotheses `h_A > 0` / `h_f > 0` — the proof has only `h_A <= h_f`.
2. "`h_f = 0` is a collinear degeneracy" — wrong; it is the right-triangle case.
3. Presenting `(2pi - sum beta)/2` as the ledger — wrong; the ledger is
   `(sum_e beta_e - pi)/2`, from `sum_e gamma_fe = pi` alone with `gamma_fe` always real.
4. My alternative corner-angle reading and the "inconsistency" I derived from it — my own
   bookkeeping error; withdrawn, nothing asserted against the proof.
5. `1 - x y <= (1-tau)/(1+tau)` — wrong direction; the lemma's `x y <= (1-tau)/(1+tau)`
   (hence `1-xy >= 2tau/(1+tau) >= tau`) is right. I reversed this twice.
6. `u x (A - O_f)` as the area expression — that is zero; the correct expression is
   `cross(O_f - u, A - u)`, as the lead's note already states.
7. "`U^2/4` for edge-disjoint packs" — wrong; that factor is for the all-faces sum.

## 7. Residual scope

Not audited here: the lead's directed-interval certification and Fraction replay of the 12
packs, and the catalogue counts. The global box bound is **already done** (per the lead),
so it is not a missing step; I withdraw my earlier characterisation of it as one.
