"""C920 INPUT EXACTNESS AUDIT (file parsing only; NO import of any lead module -- those may write).

Checks
  A. kernel_basis_diagnostic.json[0]['R']  vs  relative_stress_ball_certificate.json hex entries:
     item-by-item identical, and each binary64 hex is received EXACTLY by the decimal (singleton
     rational check: Fraction(float.fromhex(h)) == Fraction(decimal_string)).
  B. active-edge graph mapping to canonical: raw ring k -> can (k-2) mod 9, hubs unchanged;
     the 45 carrying edges must form a subgraph of the 51-edge canonical graph.
Robust discovery: scan both JSONs for hex strings / edge lists instead of assuming a schema.

Usage: py -3 -B -X utf8 research-2026/team-current/r20-stress/c920_input_exactness_audit.py
"""
import json, re
from fractions import Fraction as F
from pathlib import Path

W = Path(__file__).parent
OUT = W / 'out'
LEAD = W.parent / 'lead'
KD = json.loads((LEAD / 'kernel_basis_diagnostic.json').read_text(encoding='utf-8'))
RC = json.loads((LEAD / 'relative_stress_ball_certificate.json').read_text(encoding='utf-8'))

HEXRE = re.compile(r'^[-+]?0[xX][0-9a-fA-F]+(\.[0-9a-fA-F]*)?[pP][-+]?\d+$')
DECRE = re.compile(r'^[-+]?\d+(\.\d+)?([eE][-+]?\d+)?$')


def walk(o, path=''):
    if isinstance(o, dict):
        for k, v in o.items():
            yield from walk(v, path + '/' + str(k))
    elif isinstance(o, list):
        for i, v in enumerate(o):
            yield from walk(v, path + '[%d]' % i)
    else:
        yield path, o


R0 = KD[0].get('R')
res = {'A': {}, 'B': {}}

# ---- A: flatten R (list of 4, possibly nested) and compare with the certificate's hex entries ----
def flat(o):
    if isinstance(o, list):
        out = []
        for v in o:
            out.extend(flat(v))
        return out
    return [o]


Rflat = flat(R0)
hex_entries = [(p, v) for (p, v) in walk(RC) if isinstance(v, (str, float, int))][:0]
# collect candidate hex/decimal pairs on leaves
leaves = [(p, v) for (p, v) in walk(RC) if isinstance(v, (str,)) and (HEXRE.match(v.strip()) or DECRE.match(v.strip()))]
hexes = [(p, v) for (p, v) in leaves if HEXRE.match(v.strip())]
decs = [(p, v) for (p, v) in leaves if not HEXRE.match(v.strip())]
res['A']['n_R_entries'] = len(Rflat)
res['A']['n_hex_entries_in_cert'] = len(hexes)
res['A']['n_decimal_entries_in_cert'] = len(decs)

# exact equality: R entries (as given) vs hex entries (as exact dyadic rationals)
def exact(x):
    if isinstance(x, str):
        s = x.strip()
        if HEXRE.match(s):
            return F(float.fromhex(s))
        if DECRE.match(s):
            return F(s)
        return None
    if isinstance(x, int):
        return F(x)
    if isinstance(x, float):
        return F(x)
    return None


Rex = [exact(x) for x in Rflat]
hexex = [exact(v) for (_, v) in hexes]
res['A']['R_all_exact_rational'] = all(e is not None for e in Rex)
res['A']['cert_hex_all_exact_dyadic'] = all(e is not None for e in hexex)
if len(Rex) and len(hexex):
    n = min(len(Rex), len(hexex))
    same = [Rex[i] == hexex[i] for i in range(n)]
    res['A']['itemwise_identical'] = all(same)
    res['A']['n_compared'] = n
    res['A']['first_mismatch'] = next((i for i, s in enumerate(same) if not s), None)
    res['A']['R_values'] = [str(e) for e in Rex[:6]]
    res['A']['hex_values'] = [str(e) for e in hexex[:6]]
# singleton/decimal-exactness: does the decimal string equal the exact dyadic value?
pair_ok = []
for hp, hv in hexes:
    base = hp.rsplit('/', 1)[0]
    cand = [d for p, d in decs if p.rsplit('/', 1)[0] == base]
    if cand:
        pair_ok.append(exact(cand[0]) == exact(hv))
res['A']['decimal_receives_hex_exactly_all'] = all(pair_ok) if pair_ok else 'no hex/decimal sibling pairs found'
res['A']['n_pair_checks'] = len(pair_ok)

# ---- B: graph mapping raw k -> can (k-2) mod 9, hubs unchanged; 45 carrying vs 51 edges --------
def find_edge_lists(o, path=''):
    found = []
    if isinstance(o, dict):
        for k, v in o.items():
            found.extend(find_edge_lists(v, path + '/' + str(k)))
    elif isinstance(o, list):
        if o and all(isinstance(e, (list, tuple)) and 2 <= len(e) <= 3 and all(isinstance(z, int) for z in e) for e in o):
            found.append((path, [tuple(e) for e in o]))
        else:
            for i, v in enumerate(o):
                found.extend(find_edge_lists(v, path + '[%d]' % i))
    return found


raw_lists = find_edge_lists(KD)
cert_lists = find_edge_lists(RC)
def canon(e):
    return tuple(sorted(((x - 2) % 9 if x < 9 else x) for x in e))
res['B']['kd_edge_lists'] = [(p, len(l)) for p, l in raw_lists][:6]
res['B']['cert_edge_lists'] = [(p, len(l)) for p, l in cert_lists][:6]
if raw_lists and cert_lists:
    (_, rawE), (_, certE) = raw_lists[0], cert_lists[0]
    cset = {tuple(sorted(e)) for e in certE}
    mapped = [canon(e) for e in rawE]
    res['B']['n_raw'] = len(rawE)
    res['B']['n_cert'] = len(certE)
    res['B']['n_mapped_in_cert'] = sum(1 for m in mapped if m in cset)
    res['B']['mapped_all_subset'] = all(m in cset for m in mapped)
    res['B']['n_distinct_mapped'] = len(set(mapped))
else:
    res['B']['note'] = 'edge lists not auto-found; none compared'

OUT.mkdir(exist_ok=True)
(OUT / 'c920_input_exactness_audit.json').write_text(json.dumps(res, indent=1), encoding='utf-8')
print(json.dumps(res, indent=1)[:2400])
print('[done] -> out/c920_input_exactness_audit.json')
