"""Exact rational elementary controls for REPORT.md; not a cover certificate."""
from fractions import Fraction as Q
from pathlib import Path
import json
q = Q
x=q('.338'); a=x-x**3/6+x**5/120
x=q('.34'); b=x-x**3/6
x=q('.288'); c=x-x**3/6
x=q('.964'); d=x-x**3/6+x**5/120-x**7/5040
x=q('.676'); e=1-x**2/2+x**4/24
checks={'sin338upper_lt3317':a<q('.3317'),'sin34lower_gt332':b>q('.332'),'sin288lower_gt28':c>q('.28'),'sin964lower_gt82':d>q('.82'),'cos676upper_lt8':e<q('.8'),'radial_bound':q('.9433')**2+q('.3318')**2<1,'sqrt_bound':q('.258')**2>q('.0664'),'final_margin':(2*q('.9433')-q('.258'))*q('.82')>4*q('.332')}
out={'scope':'Exact rational elementary constants for REPORT.md; not a global optimality certificate','checks':checks,'all_pass':all(checks.values()),'final_separation_lower':str((2*q('.9433')-q('.258'))*q('.82')),'final_margin_above_1.328':str((2*q('.9433')-q('.258'))*q('.82')-q('1.328'))}
Path(__file__).with_name('rational-controls.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
assert out['all_pass']
print('8 exact rational controls passed; analytic lens/fan argument is in REPORT.md.')
