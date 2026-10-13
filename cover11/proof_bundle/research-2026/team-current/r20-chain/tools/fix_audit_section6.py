"""Surgical replacement of section 6 of ORACLE-CHART-INDEX-AUDIT.md (retraction of my
wrong off-by-one flag; correct verification per the lead's objection)."""
import io
from pathlib import Path

p = Path(__file__).resolve().parent.parent / "ORACLE-CHART-INDEX-AUDIT.md"
s = p.read_text(encoding="utf-8")
i = s.index("## 6. Reflection map")
j = s.index("## 7. Residual interfaces")

new = """## 6. Reflection map — VERIFIED CORRECT; my earlier flag is RETRACTED

**Retraction.** An earlier version of this section claimed an off-by-one index slip in the
reflection transport of `cosine_dbm_pilot.py:39` / `ORACLE-REFLECTION.md`, and also claimed
"`y = rho(y)` at this root with `y_1 = y_8`". **Both statements are wrong.** The lead caught
the first; the second is refuted by the data itself (`y_1 = 0.0042962643`,
`y_8 = 0.2972779593`). Corrected verification (`tools/reflection_recheck.py`,
`out/reflection_recheck.txt`), all at the exact root:

* **Gap identity:** `theta_{i+1} - theta_i = L - D*y_i`, so `y_i` owns the anchor gap
  `U_i` (anchor `i -> i+1`). Residuals <= 6.7e-16 over `i = 0..7`.
* **Anchor map:** `a(i) = (3-i) mod 9` is correct (anchor `U_i` touches sites `i, i+1`, and
  `p(i) = (4-i) mod 9` on sites satisfies `p(i) in {a(i), a(i+1)}`).
* **Transport:** with `theta'_i = theta_3 - theta_{(3-i) mod 9}` (unwrapped into `[0,2pi)`),
  the reflected coordinates satisfy `theta'_0 = 0` and
  `theta'_{i+1} - theta'_i = L - D*y_{(2-i) mod 9}`, i.e. **`y'_i = y_{(2-i) mod 9}` — the
  original source is RIGHT** (residuals <= 7e-16). The axis is the line through anchor 3
  (angle `theta_3`); there is no half-integer axis.
* My earlier alternative `theta'_i = theta_1 + theta_2 - theta_{(3-i) mod 9}` differs from the
  correct formula by up to `0.2044` rad at `i = 7` and is not even a chart formula (its
  `theta'_0` is not 0). It is discarded.
* **Cyclic convention:** with `rho(y)_i = y_{(2-i) mod 9}`, the claim `y_1 = y_8` / `y_2 = y_7`
  is FALSE; the actual coincidences are `y_1 = y_3` and `y_2 = y_4 = y_6`, while
  `y_i = y_{(2-i) mod 9}` holds for every `i` at this root (max deviation 0.0 over the two
  independent runs of the check). So the candidate's width vector is invariant under this
  reflection, which is a genuine observation about the candidate.
* **Self-consistency / why it is a true symmetry:** the site map `p(i) = (4-i) mod 9`, the
  anchor map `a(i) = (3-i) mod 9` and the incidence relation `p(i) in {a(i), a(i+1)}` all
  hold (checked for all nine `i`), so `V(y^R) = V(y)` exactly as `ORACLE-REFLECTION.md`
  states, and `y^R = y` at this particular root. No defect, no off-by-one.

**Residual naming point (cosmetic, no action required):** `ORACLE-REFLECTION.md` writes the
axis as "the line of angle `theta_3/2`". The composition derivation there is right; with the
chart pin `theta'_0 = 0` imposed, the composed rotation realised by `theta'_i = theta_3 -
theta_{3-i}` is by `theta_3`. This is a wording matter only.

No code in `lead/` was modified; this section is documentation only.

"""
p.write_text(s[:i] + new + s[j:], encoding="utf-8")
print("section 6 replaced; file length", len(p.read_text(encoding='utf-8')))
