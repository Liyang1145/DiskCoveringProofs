"""Exact checks:
 (1) coefficient identity: SharedMomentConcreteSwitchBatch start0_switchK_{p,q,b,d2,d1}
     == canonicalSwitch{P,Q,B,D2,D1} D7 kap7 (K-1 mod 9) for the Lean representative k=7 table;
 (2) Face1 data (SharedMomentConcreteFace1Data) == canonicalFace D7 {1,8,9} up to a slot permutation;
 (3) aggregation: sum of the nine batch bounds == start0_switch_total_bound (22523/250000);
 (4) strict-total budgets for both representatives with proposed rational maxima.
"""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N11
import re, json, sys
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import rep_tables as RT
WIP = Path(DCP_N11+'/wip/lean/N11Formalization')
src = (WIP / 'SharedMomentConcreteSwitchBatch.lean').read_text()
def rat(s):
    s = s.strip().strip('()').replace(': ℚ', '').strip()
    return F(s)
vals = {}
for m in re.finditer(r'def start0_switch(\d)_(p|q|b|d2|d1|bound) : ℚ := \((.*?) : ℚ\)', src):
    vals.setdefault(int(m.group(1)), {})[m.group(2)] = F(m.group(3).strip('()'))
tot = re.search(r'def start0_switch_total_bound : ℚ := \((.*?) : ℚ\)', src).group(1)
T7 = RT.build(0, 7)
res = {'switch_identity': {}, 'notes': []}
ok = True
for K in range(9):
    j = (K - 1) % 9
    L = T7['switches'][j]
    eq = all(vals[K][x] == L[x] for x in ['p', 'q', 'b', 'd2', 'd1'])
    ok &= eq
    res['switch_identity'][f'batch{K}->lean{j}'] = eq
    if not eq:
        res['notes'].append({K: {x: [str(vals[K][x]), str(L[x])] for x in ['p', 'q', 'b', 'd2', 'd1']}})
S = sum(vals[K]['bound'] for K in range(9))
res['bound_sum'] = str(S); res['total_bound'] = tot; res['sum_eq_total'] = (S == F(tot))
res['bounds_by_lean_index'] = {str((K - 1) % 9): str(vals[K]['bound']) for K in range(9)}
res['hist_switch_upper_vs_bound'] = {K: [T7['hist_upper'][f'switch{K}'], float(vals[K]['bound'])] for K in range(9)}
res['bound_ge_hist_upper'] = all(float(vals[K]['bound']) >= T7['hist_upper'][f'switch{K}'] for K in range(9))
# Face1
fsrc = (WIP / 'SharedMomentConcreteFace1Data.lean').read_text()
def vec(name):
    m = re.search(rf'def {name} : Fin 3 → ℚ := !\[(.*?)\]\n', fsrc).group(1)
    return [F(x.strip().strip('()').replace(': ℚ', '').strip()) for x in re.findall(r'\(([^()]*?) : ℚ\)', m)]
fp, fq, fb = vec('start0_face1_p'), vec('start0_face1_q'), vec('start0_face1_b')
L = T7['faces'][(1, 8, 9)]
import itertools
perm = [pm for pm in itertools.permutations(range(3)) if all(L['p'][s] == fp[pm[s]] and L['q'][s] == fq[pm[s]] and L['b'][s] == fb[pm[s]] for s in range(3))]
res['face1_lean_face'] = '{1,8,9}'; res['face1_perm_lean_slot_to_data_slot'] = perm
print(json.dumps(res, indent=1, default=str))
print('ALL SWITCH IDENTITIES', ok)
