"""R22 corrections: mark the four wrong sentences and record the lead's exact branch-coverage
argument. No new computations beyond a pointwise confirmation of the reasoning chain."""
import sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
from pathlib import Path

p = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\cline2-closure-kernel'
         r'\R22-NORM-A-INTERVAL-AUDIT.md')
t = p.read_text(encoding='utf-8')

# 1) header note of corrections
marker = '## Verdict'
note = """## Corrections applied after lead review (this section supersedes the text below)

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

"""
t = t.replace(marker, note + marker, 1)

# strike the wrong sentences inline
t = t.replace('which is exactly the lead\'s `[a−, a+]`, with the second band at `+pi/2` falling outside `(0,T)`\nbecause `T ≤ 2 < π`.',
              'which is exactly the lead\'s `[a−, a+]` **[the "second band at +pi/2" is WITHDRAWN — '
              'the period in A is pi, and the lead\'s exact range argument shows theta-branch only]**.')
t = t.replace('`2A + gamma in [theta, pi − theta]  (mod 2pi)`',
              '`2A + gamma in [theta, pi − theta]`  (exact, no mod needed: see corrections)')
t = t.replace('In those cases `[max(0,a−), min(T,a+)] = (0,T)` — the whole\nwedge is norm-feasible, so the formula still returns the correct set',
              '**[WITHDRAWN: that does not imply the whole wedge is feasible — the set is `[a−,T]` '
              'and `a− > 0` makes it proper]**')
t = t.replace('## 6. One domain inconsistency to resolve in the text',
              '## 6. Cap statement — WITHDRAWN (see corrections)')
t = t.replace('These cannot\nboth hold:', '**[WITHDRAWN]** As originally read by me this looked inconsistent:')
t = t.replace('Either way the **interval formula itself is unaffected**; only the admissible `T`-range needs one\nsentence.',
              'The statement is in fact a conditional implication, so there is nothing to resolve.')

p.write_text(t, encoding='utf-8')
print('corrections section added; WITHDRAWN markers:', t.count('WITHDRAWN'))
for i, l in enumerate(t.splitlines()[:16], 1):
    print(f'{i:3d}| {l}')
