"""Self-consistency of the middle_inward per-factor bounds: upper >= lower_probe always."""
import json
from pathlib import Path

LEAD = Path(__file__).resolve().parents[1] / 'lead'
print(f'{"fi":>3} {"factor":14s} {"upper":>13s} {"lower_probe":>13s} {"gap":>11s}  evals  budget')
bad = []
for fi in range(29):
    p = LEAD / f'middle_inward_bound_{fi:02d}.json'
    if not p.exists():
        print(f'{fi:>3} -              (absent)')
        continue
    d = json.loads(p.read_text())
    gap = d['upper'] - d['lower_probe']
    flag = ''
    if gap < -1e-12:
        flag = '   *** INCONSISTENT: upper < lower_probe ***'
        bad.append(fi)
    print(f'{fi:>3} {d["factor"]:14s} {d["upper"]:+.9f} {d["lower_probe"]:+.9f} '
          f'{gap:+.3e}  {d["evaluations"]:>6d}  {d["budget_ended"]}{flag}')
print()
print('inconsistent factors:', bad if bad else 'none')
