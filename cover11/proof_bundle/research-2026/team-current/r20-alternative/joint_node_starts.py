"""joint_node_starts.py  (r20-alternative; sole write, no child; NUMERIC only)

Real node starts (lead): read  ~/research-2026/team-current/lead/adaptive_stellar_pilot.json
(nodes list; nodes[20]['vertices'] and nodes[26]['vertices'] are 9x9 rational strings) and take
the CENTROID of each node's nine vertices with exact Fractions: sum(Fraction(v[i]))/9.
NO fallback: raise if the file/schema is missing.  Only these two starts are run, with the
audited y-chain-rule Jacobian of joint_oracle_attack_new4 (whose CS gate must pass first).
Records are appended to joint_oracle_attack_new4.json under 'node_starts_real'.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np

import joint_oracle_attack_new4 as J

OUT = Path(__file__).resolve().parent
PILOT = OUT.parent / 'lead' / 'adaptive_stellar_pilot.json'


def node_centroid(node_key):
    d = json.loads(PILOT.read_text(encoding='utf-8'))
    nodes = d['nodes']
    rec = nodes[int(node_key)]
    verts = rec['vertices']
    assert len(verts) == 9 and all(len(v) == 9 for v in verts), 'vertices must be 9x9'
    cen = [sum(F(str(v[i])) for v in verts) / 9 for i in range(9)]
    vals = [float(x) for x in cen]
    s = sum(vals)
    kind = 'widths' if abs(s - 2 * np.pi) < 1e-6 else ('y' if abs(s - 1.0) < 1e-6 else 'unknown')
    if kind == 'widths':
        y9 = [(J.L_CAP - v) / J.D_CAP for v in vals]
    elif kind == 'y':
        y9 = vals
    else:
        raise ValueError('node %s vertices: sum = %.6f, neither 2*pi (widths) nor 1 (y)' %
                         (node_key, s))
    return {'node': int(node_key), 'sum_of_centroid': s, 'kind_detected': kind,
            'y9': y9, 'y8': y9[:8]}


if __name__ == '__main__':
    chk = J.jac_cs_check()
    print('jac CS gate:', chk['PASS_lt_1e-6'], 'max err %.3e' % chk['max_jac_error'])
    if not chk['PASS_lt_1e-6']:
        raise SystemExit('jacobian gate failed; not running')
    rec = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': J.R_STAR,
           'source': str(PILOT), 'jacobian_cs_check': chk, 'runs': []}
    for key in (20, 26):
        info = node_centroid(key)
        s = J.solve(np.asarray(info['y8'], dtype=float))
        s.update({'start': 'node%d_centroid' % key, 'node_info': info})
        s['V_minus_R_star'] = s['r'] - J.R_STAR
        s['below_R_star_by_1e7'] = bool(s['r'] < J.R_STAR - 1e-7
                                        and s['min_edge_residual_all51'] > -1e-9
                                        and s['widths_max_leq_L'])
        rec['runs'].append(s)
        print('node%-3d centroid(%s) r=%.9f r-R*=%.3e success=%s min51=%.1e wmaxOK=%s' %
              (key, info['kind_detected'], s['r'], s['V_minus_R_star'], s['success'],
               s['min_edge_residual_all51'], s['widths_max_leq_L']))
    tgt = OUT / 'joint_oracle_attack_new4.json'
    old = json.loads(tgt.read_text(encoding='utf-8')) if tgt.exists() else {}
    old['node_starts_real'] = rec
    old['note_node_starts'] = ('real node20/node26 centroid starts with exact Fraction centroid; '
                               'previous fallback entries in "runs" are superseded for these two '
                               'starts only; the other two starts are not re-run')
    tgt.write_text(json.dumps(old, indent=2), encoding='utf-8')
    print('n_below =', int(sum(1 for s in rec['runs'] if s['below_R_star_by_1e7'])),
          '-> updated joint_oracle_attack_new4.json')
