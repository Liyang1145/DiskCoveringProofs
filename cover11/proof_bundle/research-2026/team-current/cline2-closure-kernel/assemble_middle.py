"""Assemble the middle-inward per-factor bounds and compare with the frozen numeric_total."""
import json, math
from pathlib import Path

L = Path(__file__).resolve().parents[1] / 'lead'
z = [float(v) for v in json.loads((L / 'middle_inward_frozen.json').read_text())['z']]
pi = math.pi
R = 0.38
const = (pi * (sum(z[:9]) + 2 * sum(z[9:11]) + sum(z[50:71]) - 2 * z[71] - 2 * z[72])
         + 2 * z[72] * math.asin(2 * R) - pi * sum(z[112:]))
frozen = json.loads((L / 'middle_inward_frozen.json').read_text())
print('constant part        =', const)
print('frozen numeric_total =', frozen['numeric_total'])

rows = []
tot = 0.0
for fi in range(29):
    f = L / f'middle_inward_bound_{fi:02d}.json'
    if f.exists():
        d = json.loads(f.read_text())
        rows.append((fi, d['factor'], d['upper'], d['evaluations'], d['budget_ended']))
        tot += d['upper']
    else:
        rows.append((fi, 'MISSING', None, None, None))
print('\nper-factor bounds:')
for fi, nm, u, ev, be in rows:
    us = f'{u:+.9f}' if u is not None else '-'
    print(f'  {fi:2d} {nm:14s} {us:>14s}  evals={ev} budget_ended={be}')
print(f'\nsum of available bounds = {tot:.9f}')
print(f'constant + sum          = {const + tot:.9f}')
print(f'frozen numeric_total    = {frozen["numeric_total"]:.9f}')
print(f'difference              = {frozen["numeric_total"] - (const + tot):+.6f}')
print(f'\npi = {pi:.9f};  margin pi - (constant+sum) = {pi - (const + tot):+.6f}')
