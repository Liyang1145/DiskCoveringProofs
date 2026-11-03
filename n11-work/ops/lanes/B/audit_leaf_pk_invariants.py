#!/usr/bin/env python3
"""Correct structural invariants for the 14 All14 archive-refinement leaves.

The committed `preflight_lane_b_archive_leaves.py` requires `pk<i>`/`valid<i>`
indices to be exactly 0..K-1 and therefore reports `ok:false` for every leaf.
That expectation is wrong: the leaves *deduplicate* packets -- they define only
the distinct `pk<i>` and fill the length-K `pk` vector by repeating earlier
entries (e.g. EnergyRefineN0038 has 14 defs, K=27, vector starts
`![pk2,pk2,pk2,pk2,pk2,pk5,...]`).  The real invariants are:
  (a) pk vector length == K;
  (b) every vector entry names a defined `pk<i>`;
  (c) the set of `valid<i>` theorems is exactly the set of defined `pk<i>`;
  (d) newIDs is the singleton {id}.
Static source only; NOT a build and NOT a proof.
"""
from __future__ import annotations
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
    r = {'module': module, 'id': ident, 'problems': []}
    p = os.path.join(LEAN, module + '.lean')
    if not os.path.exists(p):
        r['problems'].append('missing file'); return r
    s = open(p, encoding='utf-8').read()
    mK = re.search(r'abbrev K :=\s*(\d+)', s)
    if not mK:
        r['problems'].append('no abbrev K'); return r
    K = int(mK.group(1)); r['K'] = K
    pkdefs = set(re.findall(r'def (pk\d+)\s*:', s))
    valids = set(re.findall(r'theorem (valid\d+)\s*:', s))
    r['pk_defs'], r['valids'] = len(pkdefs), len(valids)
    mv = re.search(r'def pk : Fin K . MPacket := !\[(.*?)\]', s, re.S)
    if not mv:
        r['problems'].append('no pk vector')
    else:
        entries = [x.strip() for x in mv.group(1).split(',')]
        r['pk_vector_len'] = len(entries)
        if len(entries) != K:
            r['problems'].append('pk vector len %d != K %d' % (len(entries), K))
        undef = sorted({e for e in entries if e not in pkdefs})
        if undef:
            r['problems'].append('undefined vector entries %r' % undef[:3])
    if {v.replace('valid', 'pk') for v in valids} != pkdefs:
        r['problems'].append('valid set != pk def set')
    mn = re.search(r'def newIDs : Finset \(Fin 5011\) := \{(\d+)\}', s)
    if not mn:
        r['problems'].append('no newIDs singleton')
    elif int(mn.group(1)) != ident:
        r['problems'].append('newIDs != id')
    else:
        r['newIDs'] = int(mn.group(1))
    return r


def main():
    rows = [check(m, i) for m, i in LEAVES]
    ok = all(not r['problems'] for r in rows)
    rep = {'ok': ok, 'scope': 'static source invariants; not a build, not a proof',
           'invariants': ['veclen==K', 'all entries defined', 'valid set == pk def set',
                          'newIDs==id'], 'leaves': rows}
    out = os.path.join(HERE, 'audit_leaf_pk_invariants-report.json')
    json.dump(rep, open(out, 'w'), indent=1)
    for r in rows:
        print('%-26s K=%-3s pkdefs=%-3s valids=%-3s veclen=%-3s %s' % (
            r['module'], r.get('K'), r.get('pk_defs'), r.get('valids'),
            r.get('pk_vector_len'), 'ok' if not r['problems'] else 'PROBLEM ' + '; '.join(r['problems'])))
    print('RESULT', 'OK' if ok else 'PROBLEMS')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
