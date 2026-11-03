#!/usr/bin/env python3
"""Static preflight for the 14 archive-refinement leaf modules consumed by
LaneBArchiveRefineAll14: contiguous node/pk/valid indices, valid<i> checking
pk<i>, pk vector length == K, newIDs singleton == claimed id, and new_radius
signature == ResidualRadiusCertificate (Fin 9 chart arg, matrix ... 4096 n).
Static source only; NOT a build and NOT a proof.
"""
import json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.abspath(os.path.join(HERE, '..', '..', '..', 'lean', 'N11Formalization'))

LEAVES = [('EnergyRefineN0003Restored', 3), ('EnergyRefineN0023Restored', 23),
          ('EnergyRefineN0038', 38), ('EnergyRefineN3432', 3432),
          ('EnergyRefineN3490', 3490), ('EnergyRefineN3517', 3517),
          ('EnergyRefineN3550', 3550), ('EnergyRefineN3564', 3564),
          ('EnergyRefineN3569', 3569), ('EnergyRefineN3578', 3578),
          ('EnergyRefineN3738', 3738), ('EnergyRefineN3781', 3781),
          ('EnergyRefineN3825', 3825), ('EnergyRefineN3854', 3854)]


def check(module, ident):
    p = os.path.join(LEAN, module + '.lean')
    r = {'module': module, 'id': ident, 'problems': []}
    if not os.path.exists(p):
        r['problems'].append('missing file')
        return r
    s = open(p, encoding='utf-8').read()
    r['bytes'] = len(s.encode('utf-8'))
    r['lines'] = s.count('\n')
    mk = re.search(r'abbrev K :=\s*(\d+)', s)
    if not mk:
        r['problems'].append('no abbrev K')
        return r
    K = int(mk.group(1))
    r['K'] = K
    nodes = sorted(int(x) for x in re.findall(r'def node(\d+)\s*:', s))
    pks = sorted(int(x) for x in re.findall(r'def pk(\d+)\s*:', s))
    val = sorted(int(x) for x in re.findall(r'theorem valid(\d+)\s*:', s))
    r['nodes'], r['pk_defs'], r['valids'] = len(nodes), len(pks), len(val)
    if nodes != list(range(K)):
        r['problems'].append('node idx != 0..K-1')
    if pks != list(range(K)):
        r['problems'].append('pk idx != 0..K-1')
    if val != list(range(K)):
        r['problems'].append('valid idx != 0..K-1')
    for i, ref in re.findall(r'theorem valid(\d+)\s*:\s*MValid pk(\d+)', s):
        if i != ref:
            r['problems'].append('valid%s->pk%s' % (i, ref))
    mv = re.search(r'def pk : Fin K → MPacket := !\[(.*?)\]', s, re.S)
    if not mv:
        r['problems'].append('no pk vector')
    else:
        e = [x.strip() for x in mv.group(1).split(',')]
        r['pk_vector_len'] = len(e)
        if len(e) != K:
            r['problems'].append('pk vector len %d != K %d' % (len(e), K))
        bad = [x for x in e if not re.fullmatch(r'pk\d+', x)]
        if bad:
            r['problems'].append('non-packet entries %r' % bad[:3])
    mn = re.search(r'def newIDs : Finset \(Fin 5011\) := \{(\d+)\}', s)
    if not mn:
        r['problems'].append('no newIDs singleton')
    else:
        r['newIDs'] = int(mn.group(1))
        if int(mn.group(1)) != ident:
            r['problems'].append('newIDs != id')
    i = s.find('theorem new_radius')
    if i < 0:
        r['problems'].append('no new_radius')
    else:
        seg = s[i:i + 800]
        if not re.search(r'\(y\s*:\s*Fin 9 → ℝ\)', seg):
            r['problems'].append('new_radius y != Fin 9 -> R')
        if 'DBMSourceTree.data 4096 n' not in seg:
            r['problems'].append('new_radius matrix != 4096 n')
    return r


def main():
    rows = [check(m, i) for m, i in LEAVES]
    ok = all(not r['problems'] for r in rows)
    rep = {'ok': ok, 'scope': 'static preflight; not a build', 'leaves': rows}
    out = os.path.join(HERE, 'preflight_lane_b_archive_leaves-report.json')
    json.dump(rep, open(out, 'w'), indent=1)
    for r in rows:
        print('%-28s id=%-5s K=%-4s pklen=%-4s %s' % (
            r['module'], r['id'], r.get('K'), r.get('pk_vector_len'),
            'ok' if not r['problems'] else 'PROBLEM: ' + '; '.join(r['problems'])))
    print('RESULT', 'OK' if ok else 'PROBLEMS')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
