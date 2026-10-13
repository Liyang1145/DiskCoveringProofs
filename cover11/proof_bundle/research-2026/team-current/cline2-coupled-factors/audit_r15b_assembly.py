"""cline2-coupled-factors R15b audit: verify the lead's assembly arithmetic, the 7+22
partition, the broad-domain claim, and the digest cleanliness of the 22 records.

Read-only with respect to the lead's directory: the lead's own constant/assembly formulas
are re-evaluated here on my records and compared to the numbers published in
lead/LOCAL-Q0-FLAT-EXCLUSION.md and lead/assemble_current_patch.py.  No 22 factor is
recomputed, no coefficient is optimized.
"""
import os, json, hashlib, glob
from pathlib import Path
from mpmath import iv

iv.dps = 40
HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / 'lead'
canonical = LEAD / 'joint_nested_frozen.json'
digest = hashlib.sha256(canonical.read_bytes()).hexdigest()
z = [iv.mpf(f'{x:.9f}') for x in json.loads(canonical.read_text())['z']]
print('frozen file  :', canonical.name)
print('sha256       :', digest)
print('len(z)       :', len(z), ' z[50:73] all zero:',
      all(x == 0 for x in z[50:73]))

# ---- the lead's constant, exactly as assemble_current_patch.py:7 computes it ----
const = (iv.pi*(sum(z[:9]) + 2*sum(z[9:11]) + sum(z[50:71]) - 2*z[71] - 2*z[72])
         - iv.pi*sum(z[112:]))
print('\n--- constant ---')
print('const (lead formula, incl -2*z[72])      =', const)
print('const with the eta term dropped (z72=0)  =',
      iv.pi*(sum(z[:9]) + 2*sum(z[9:11]) + sum(z[50:71]) - 2*z[71]) - iv.pi*sum(z[112:]))
print('z[72]                                    =', z[72])
print('the two agree because z[72] == 0; the DOC line 5 quotes kernel line 110 which is')
print('   pi*(sum z0..8 + 2 sum z9..10 + sum z50..70 - 2 z71) + 2 z72 asin(2R) - pi sum z112..')
print('   i.e. it carries +2 z72 asin(2R) and no -2 z72 term; with z72 == 0 all forms coincide.')

# ---- partition check ----
SKIP = [1, 2, 12, 13, 21, 22, 23]
ids = [i for i in range(29) if i not in SKIP]
print('\n--- 7 + 22 partition ---')
print('skipped (C854) :', SKIP, f'({len(SKIP)})')
print('assembled (22) :', ids, f'({len(ids)})')
print('overlap        :', sorted(set(SKIP) & set(ids)))
print('union == 0..28 :', sorted(set(SKIP) | set(ids)) == list(range(29)))

# ---- record audit: glob shape, digest, staleness ----
folder = HERE / 'out' / ('r15_' + digest[:12])
print('\n--- record audit in', folder.name, '---')
paths = {}
for i in ids:
    got = list(folder.glob(f'*bound_{i:02d}.json'))
    paths[i] = got
    if len(got) != 1:
        print(f'   PROBLEM factor {i:2d}: glob "*bound_{i:02d}.json" matched {len(got)}')
extra = [p.name for p in folder.glob('*bound_*.json')
         if int(p.name.split('_')[-1].split('.')[0]) not in ids]
print('   extra *bound_* files for indices outside the 22:', extra)
stale = []
summ = iv.mpf(0)
rows = []
for i in ids:
    p = paths[i][0]
    d = json.loads(p.read_text())
    raw = p.read_bytes()
    ok_digest_field = (d.get('coefficient_sha256') == digest)
    # stale-byte check: the record must contain the CURRENT digest hex and no other
    hexes = {h for h in [digest, 'a856f2c12bcc24c428c2ac6044f81877059cc3039f73db992dc5e3e004c23636',
                         'adf07c491585cfe536876da071f25b7707833eb05b39a053d920e15ee42e0eab']
             if h.encode() in raw}
    summ += iv.mpf(d['upper'])
    rows.append((i, d['factor'], d['upper'], ok_digest_field, sorted(hexes)))
    if not ok_digest_field:
        stale.append(i)
print(f'   records found: {len(ids)}/22   digest-field mismatches: {stale}')
print('   per-record embedded digest hexes (should be exactly the current one):')
bad = [r for r in rows if r[4] != ['5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb']]
for r in rows:
    tag = '' if r[4] == ['5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb'] else '  <-- UNEXPECTED'
    print(f'      fi={r[0]:2d} {r[1]:9s} digest_ok={r[3]} hexes={[h[:12] for h in r[4]]}{tag}')
print(f'   records with unexpected digest bytes: {[r[0] for r in bad]}')

# ---- reproduce the published assembly ----
print('\n--- assembly ---')
c22 = const + summ
print('sum22                 =', summ)
print('constant + sum22      =', c22)
local = iv.mpf('28.1044')
tot = c22 + local
print('+ local 28.1044       =', tot)
print('strictly below pi     =', bool(tot.b < iv.pi.a))
print('margin  pi - total    =', iv.pi - tot)
print('required patch thresh =', iv.pi - c22)
print('\npublished in LOCAL-Q0-FLAT-EXCLUSION.md:')
print('   constant+sum22 in [-24.965452762182836329630301543233162870298784,')
print('                     -24.9654527621828363296303015432331628702947432]')
print('   total <= 3.138947237817163670369698456766837129705606 , margin 0.00264541577')
