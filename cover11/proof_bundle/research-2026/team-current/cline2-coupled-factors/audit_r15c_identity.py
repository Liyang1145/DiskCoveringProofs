"""cline2-coupled-factors R15b: test the EXACT coefficient identity behind the assembly
constant, independently of any factor bound.

Claim under audit (LOCAL-Q0-FLAT-EXCLUSION.md line 5-7): on an actual cover the matching /
angle / closure terms cancel, and the constant is
    const = pi*(sum(z0..8) + 2 sum(z9..10)) - pi*sum(z112..120)
(this is certify_q0_closure.py:110 evaluated at z[72] = 0).
Then the total dual bound is  const + (sum of the 29 atom bounds), and the arithmetic
identity that C859 relies on is that the COEFFICIENT of each z-index over the 29 atoms
equals what the constant and the seven-factor C854 value account for:
    const + 28.1044 + sum22 = 3.138947237817163671...  < pi.
We test the identity at the coefficient level by checking that
    (dual constant) + (exact sum of ALL 29 atom coefficient contributions) = pi
on a genuine cover: equivalently that the seven-factor sum is exactly the algebraic
expression pi*(sum z0..8 + 2 sum z9..10) - pi*sum z112..120 - const - (22-atom sum),
which is what the assembly asserts.  Everything here is interval arithmetic at 60 dps.
"""
import json, hashlib
from pathlib import Path
from mpmath import iv

iv.dps = 60
HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / 'lead'
canonical = LEAD / 'joint_nested_frozen.json'
digest = hashlib.sha256(canonical.read_bytes()).hexdigest()
z9 = json.loads(canonical.read_text())['z']
z = [iv.mpf(f'{x:.9f}') for x in z9]

SKIP = [1, 2, 12, 13, 21, 22, 23]
ids = [i for i in range(29) if i not in SKIP]

const = iv.pi*(sum(z[:9]) + 2*sum(z[9:11]) + sum(z[50:71]) - 2*z[71] - 2*z[72]) \
    - iv.pi*sum(z[112:])
folder = HERE/'out'/('r15_'+digest[:12])
sum22 = iv.mpf(0)
for i in ids:
    d = json.loads((folder/f'joint_patch_tight_bound_{i:02d}.json').read_text())
    sum22 += iv.mpf(d['upper'])

print('--- the two candidate expressions for the seven-factor contribution ---')
exprA = iv.pi*sum(z[i] for i in SKIP)              # pi * (sum of the 7 z-coefficients)
exprB = iv.pi*sum(z[:9]) + 2*iv.pi*sum(z[9:11]) - iv.pi*sum(z[112:])   # full coefficient
print('A  pi*sum(z over the 7 skipped)         =', exprA)
print('B  pi*sum(z0..8)+2pi*sum(z9..10)-pi*sum(z112..120) =', exprB)
print('(A - B)/pi =', (exprA-exprB)/iv.pi)
print('  -> A and B differ: the seven-atom coefficient sum is NOT simply pi*sum7z.')
print('     The remaining coefficient is carried by the constant and the 22 atoms, so the')
print('     identity must be tested at the level of the TOTAL, not of the 7 alone.')

print('\n--- total at the recorded values ---')
print('const            =', const)
print('sum22            =', sum22)
print('C854 local value = 28.1044 (rounded) / 28.10439974622152 (C854 exact)')
tot = const + sum22 + iv.mpf('28.1044')
print('const + sum22 + 28.1044            =', tot)
print('const + sum22 + 28.10439974622152  =', const + sum22 + iv.mpf('28.10439974622152'))
print('pi                                 =', iv.pi)
print('strictly below pi (rounded value)  =', bool(tot.b < iv.pi.a))
print('pi - total (rounded)               =', iv.pi - tot)

print('\n--- exact rational check of the coefficient part (z9 decimals are exact rationals) ---')
from fractions import Fraction
zf = [Fraction(f'{x:.9f}') for x in z9]
c = Fraction(0)
for i in range(9):
    c += zf[i]
for i in range(9, 11):
    c += 2*zf[i]
for i in range(50, 71):
    c += zf[i]
c -= 2*zf[71] + 2*zf[72]
for i in range(112, 121):
    c -= zf[i]
print('sum of the 121 signed coefficients (constant block) =', c)
print('as a float =', float(c), ' pi*that =', float(c)*3.141592653589793)
print('exact rational of the sum22 part:')
s22 = Fraction(0)
for i in ids:
    d = json.loads((folder/f'joint_patch_tight_bound_{i:02d}.json').read_text())
    s22 += Fraction(d['upper'])
print('   sum22 =', s22, ' (binary float read exactly)')
print('   float =', float(s22))
print('local 28.1044 as exact decimal =', Fraction('28.1044'))
tot_exact = (Fraction(str(io)) if False else None)
from mpmath import mp
mp.dps = 60
cpi = mp.pi*mp.mpf(c.numerator)/mp.mpf(c.denominator)
print('\n--- high precision total with exact coefficient rational ---')
print('const+sum22+28.1044 (exact rational constant) =',
      cpi + mp.mpf(s22.numerator)/mp.mpf(s22.denominator) + mp.mpf('28.1044'))
print('pi - that =', mp.pi - (cpi + mp.mpf(s22.numerator)/mp.mpf(s22.denominator)
                            + mp.mpf('28.1044')))
