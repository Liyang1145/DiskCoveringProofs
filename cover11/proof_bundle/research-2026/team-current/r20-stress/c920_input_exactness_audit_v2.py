"""C920 INPUT EXACTNESS AUDIT v2 -- exactly the two checks the lead specified.

A. iv singleton / exact binary64 reception (independent mpmath; NO lead-module import):
   iv.dps = 50 ; for each of the 16 floats x (R entries from kernel_basis_diagnostic.json[0]['R']):
       v = iv.mpf(x) ; check  v._mpi_[0] == v._mpi_[1]   (singleton)
       and reconstruct Fraction from the (sign, mantissa, exp, bits) tuple, compare with Fraction(x).
B. carrying-edge graph vs canonical 51-edge graph:
   The edge/face lists are NOT in JSON.  Explicitly re-copied (no import):
     raw   : interval_network_envelope.py L21 F=[[2,9,10],[6,9,10]]+[[k,(k+1)%9, 9 if 2<=k<=5 else 10]
                                               for k in [1,2,3,4,5,6,8]]
             L28-30 edges: for k in 0..8: (9+k,k),(9+(k+1)%9,k) ; then (9+s,20+j) for s in f, j over F
     canon : simplex_tree_pilot.py L11-12 faces=[[9,k,k+1] k<4]+[[10,k,(k+1)%9] 4<=k<9]+[[9,10,0],[9,10,4]]
             edges: [e for s in range(9) for e in [(9+s,s),(9+s,(s-1)%9)]] + [(9+s,20+j) for j,f in
                    enumerate(faces) for s in f]
   Map raw ring k -> (k-2) mod 9 (hubs 9,10 unchanged), compare via SORTED SITE TRIPLES.
"""
import json
from fractions import Fraction as F
from pathlib import Path
from mpmath import iv, mp

iv.dps = 50
mp.dps = 60
W = Path(__file__).parent
LEAD = W.parent / 'lead'
OUT = W / 'out'
R0 = json.loads((LEAD / 'kernel_basis_diagnostic.json').read_text(encoding='utf-8'))[0]['R']


def flat(o):
    out = []
    for v in (o if isinstance(o, list) else [o]):
        out.extend(flat(v) if isinstance(v, list) else [v])
    return out


xs = flat(R0)
res = {'A': {'n_floats': len(xs), 'all_binary64': all(isinstance(x, float) for x in xs)}, 'B': {}}
# ---- A
singleton, frac_ok, rows = 0, 0, []
for x in xs:
    v = iv.mpf(x)
    try:
        s0, s1 = v._mpi_[0], v._mpi_[1]
        is_single = (s0 == s1)
        sign, man, exp, bc = s0
        if man == 0:
            val = F(0)
        else:
            val = F(man) * F(2) ** exp      # mpmath convention: value = man * 2^exp
            if sign:
                val = -val
        eq = (val == F(x))
        singleton += int(is_single)
        frac_ok += int(eq)
        rows.append({'x': repr(x), 'singleton': bool(is_single), 'mpf_tuple': [sign, str(man), exp, bc],
                     'reconstructed': str(val), 'equals_Fraction_x': bool(eq)})
    except Exception as e:
        rows.append({'x': repr(x), 'error': str(e)})
res['A'].update({'n_singleton': singleton, 'n_fraction_equal': frac_ok, 'rows': rows[:3],
                 'all_singleton': singleton == len(xs), 'all_fraction_equal': frac_ok == len(xs)})
print('=== A: iv singleton + exact binary64 reception (iv.dps=50) ===')
print('   16 floats: %d ; singleton: %d ; Fraction(tuple) == Fraction(x): %d'
      % (len(xs), singleton, frac_ok))

# ---- B (explicit lists, no import)
rawF = [[2, 9, 10], [6, 9, 10]] + [[k, (k + 1) % 9, 9 if 2 <= k <= 5 else 10] for k in [1, 2, 3, 4, 5, 6, 8]]
rawE = []
for k in range(9):
    rawE.extend([(9 + k, k), (9 + (k + 1) % 9, k)])
for j, f in enumerate(rawF):
    rawE.extend((9 + s, 20 + j) for s in f)
canF = [[9, k, k + 1] for k in range(4)] + [[10, k, (k + 1) % 9] for k in range(4, 9)] + [[9, 10, 0], [9, 10, 4]]
canE = [e for s in range(9) for e in [(9 + s, s), (9 + s, (s - 1) % 9)]] + \
       [(9 + s, 20 + j) for j, f in enumerate(canF) for s in f]
shift = lambda t: (t - 2) % 9 if t < 9 else t
# Node layout in BOTH files: X = U + C + Z  =>  tie k |-> node k ; site s |-> node 9+s ; aux j |-> 20+j
canF_set = {tuple(sorted(f)) for f in canF}
aux_of = {tuple(sorted(f)): 20 + j for j, f in enumerate(canF)}
raw_face_to_can_aux = {20 + j: aux_of[tuple(sorted(map(shift, f)))] for j, f in enumerate(rawF)}
site_shift = lambda s: shift(s)                      # 0..8 rings; 9,10 hubs unchanged
def mape(n):
    if n < 9:                                        # tie k
        return shift(n)
    if n < 20:                                       # site s = n-9
        return 9 + site_shift(n - 9)
    return raw_face_to_can_aux[n]                    # aux
rawE_mapped = [tuple(sorted((mape(u), mape(v)))) for (u, v) in rawE]
node_map = {'ties_0_8': 'k -> (k-2) mod 9', 'sites_9_19': 's -> (s-2) mod 9 for s<9, hubs 9,10 fixed',
            'aux_20_j': {str(k): v for k, v in sorted(raw_face_to_can_aux.items())}}
canE_set = {tuple(sorted(e)) for e in canE}
rawF_mapped = [tuple(sorted(map(shift, f))) for f in rawF]
canF_set = {tuple(sorted(f)) for f in canF}
res['B'] = {'node_map': node_map, 'aux_reindex_map': {str(k): v for k, v in sorted(raw_face_to_can_aux.items())}, 'n_rawF': len(rawF), 'n_rawE': len(rawE), 'n_canF': len(canF), 'n_canE': len(canE),
            'n_distinct_canE': len(canE_set),
            'rawF_mapped_all_in_canF': all(f in canF_set for f in rawF_mapped),
            'rawE_mapped_all_in_canE': all(e in canE_set for e in rawE_mapped),
            'n_mapped_in_canE': sum(1 for e in rawE_mapped if e in canE_set),
            'n_distinct_mapped': len(set(rawE_mapped)),
            'rawF_mapped': [list(f) for f in rawF_mapped],
            'canonical_edges_not_hit': [list(e) for e in sorted(canE_set - set(rawE_mapped))]}
print('=== B: carrying edges (45) vs canonical graph (51) ===')
print('   rawF %d -> mapped all in canonical 11 faces: %s' % (len(rawF), res['B']['rawF_mapped_all_in_canF']))
print('   rawE %d (distinct %d) -> mapped all in canonical %d edges: %s (%d/%d)'
      % (len(rawE), res['B']['n_distinct_mapped'], len(canE_set), res['B']['rawE_mapped_all_in_canE'],
         res['B']['n_mapped_in_canE'], len(rawE)))
OUT.mkdir(exist_ok=True)
(OUT / 'c920_input_exactness_audit_v2.json').write_text(json.dumps(res, indent=1), encoding='utf-8')
print('[done] -> out/c920_input_exactness_audit_v2.json')
