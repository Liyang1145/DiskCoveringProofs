"""near_attack.py  (r20-alternative; sole write, no child; NUMERIC only)

Independent bounded counterexample attack near the candidate, per lead:
  * uses the AUDITED joint oracle (all 51 constraints x 53 variables Jacobian incl. the 8
    y-directions; CS gate must pass) from joint_oracle_attack_new4;
  * starts: the deepest open-cut adversary representatives from
    lead/cosine_dbm_cuts.json (up to 3) plus the candidate along the lowest critical direction
    +-0.01 (2 starts);
  * at most 6 starts, <= 400 SLSQP iterations each;
  * the criterion is r compared with R* (NOT the optimizer success flag);
  * no finding is NOT a global statement.
Caliber: canonical fan rings 0..3 / 4..8, labels 9 = hub B (raw 2), 10 = hub A (raw 0);
R* = C529 rational (NOT C891).
"""
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np

import joint_oracle_attack_new4 as J

OUT = Path(__file__).resolve().parent
CUTS = OUT.parent / 'lead' / 'cosine_dbm_cuts.json'


def to_y(vals):
    v = [float(x) for x in vals[:9]]
    s = sum(v)
    if abs(s - 2 * np.pi) < 1e-6:                       # widths
        y = [(J.L_CAP - x) / J.D_CAP for x in v]
    elif abs(s - 1.0) < 1e-6:                            # deficits
        y = v
    else:
        y = None
    return y


def hunt_adversaries():
    """depth-first search for the deepest open cuts and their representative points"""
    d = json.loads(CUTS.read_text(encoding='utf-8'))
    found = []
    PKEYS = ('y', 'y9', 'y8', 'widths', 'w', 'point', 'rep', 'vertex', 'u', 'x', 'adversary',
             'centroid', 'center')

    def first_point(obj):
        for k in PKEYS:
            if k in obj:
                v = obj[k]
                if isinstance(v, (list, tuple)) and len(v) >= 9:
                    y = to_y(v)
                    if y is not None:
                        return y
        return None
    # direct pass over 'nodes' / 'proposals' lists first
    for lk in ('nodes', 'proposals', 'fields'):
        seq = d.get(lk)
        if isinstance(seq, list):
            for rec in seq:
                if isinstance(rec, dict):
                    y = first_point(rec)
                    if y is not None and not rec.get('closed', False):
                        found.append({'depth': rec.get('depth'), 'y9': y, 'where': lk,
                                      'keys': sorted(rec.keys())[:14]})
                    elif isinstance(rec.get('nodes'), list):
                        for sub in rec['nodes']:
                            if isinstance(sub, dict):
                                y2 = first_point(sub)
                                if y2 is not None and not sub.get('closed', False):
                                    found.append({'depth': sub.get('depth', rec.get('depth')),
                                                  'y9': y2, 'where': lk + '.nodes',
                                                  'keys': sorted(sub.keys())[:14]})

    def walk(obj, depth=0):
        if len(found) >= 40:
            return
        if isinstance(obj, dict):
            keys = set(obj.keys())
            if obj.get('status') in ('open', 'OPEN') or 'open' in keys:
                y = None
                for k in ('y', 'y9', 'widths', 'w', 'adversary', 'point', 'rep', 'vertex'):
                    if k in obj:
                        y = to_y(obj[k]) if isinstance(obj[k], (list, tuple)) else None
                        if y is not None:
                            break
                if y is not None:
                    found.append({'depth': obj.get('depth', depth), 'y9': y, 'keys': sorted(keys)[:12]})
            for v in obj.values():
                walk(v, depth + 1)
        elif isinstance(obj, list):
            for v in obj:
                walk(v, depth + 1)
    walk(d)
    found.sort(key=lambda r: -(r['depth'] or 0))
    return d, found


if __name__ == '__main__':
    chk = J.jac_cs_check()
    print('jac CS gate:', chk['PASS_lt_1e-6'], 'max err %.3e' % chk['max_jac_error'])
    if not chk['PASS_lt_1e-6']:
        raise SystemExit('jacobian gate failed')
    d, adv = hunt_adversaries()
    print('cuts file top-level keys:', list(d.keys())[:10], '| adversaries found:', len(adv))
    C = J.load_centres() if hasattr(J, 'load_centres') else None
    from fixed_oracle_force_proposal import load_centres, switches_from_centres
    sw = switches_from_centres(load_centres())
    th = np.array([np.arctan2(p[1], p[0]) for p in sw])
    wc = np.mod(np.diff(np.concatenate([th, [th[0] + 2 * np.pi]])), 2 * np.pi)
    ycand = (J.L_CAP - wc) / J.D_CAP
    k_low = min(int(np.argmax(ycand)), 7)              # lowest critical direction proxy: max deficit
    starts = []
    for i, a in enumerate(adv[:3]):
        starts.append(('cut_adversary%d_depth%s' % (i, a['depth']), np.asarray(a['y9'][:8])))
    for sgn in (+1, -1):
        ys = ycand[:8].copy()
        ys[k_low] = max(0.0, min(1.0, ys[k_low] + sgn * 0.01))
        starts.append(('candidate_lowdir_%+0.2f' % (sgn * 0.01), ys))
    starts = starts[:6]
    rep = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': J.R_STAR,
           'source': str(CUTS), 'n_adversaries_found': len(adv),
           'adversary_keys_seen': adv[0]['keys'] if adv else None,
           'jacobian_cs_check': chk, 'lowest_direction_index': k_low,
           'note': ('bounded numeric attack; criterion = r vs R* (not the optimizer success flag); '
                    'no finding is NOT a global statement'),
           'runs': []}
    for name, y8 in starts:
        try:
            s = J.solve(np.asarray(y8, dtype=float))
            s.update({'start': name, 'V_minus_R_star': s['r'] - J.R_STAR})
            s['below_R_star'] = bool(s['r'] < J.R_STAR)
            s['below_R_star_by_1e7_feasible'] = bool(s['r'] < J.R_STAR - 1e-7
                                                     and s['min_edge_residual_all51'] > -1e-9
                                                     and s['widths_max_leq_L'])
        except Exception as exc:                        # noqa: BLE001
            s = {'start': name, 'error': '%s: %s' % (type(exc).__name__, exc)}
        rep['runs'].append(s)
        print('%-32s r=%.9f r-R*=%.3e (success=%s) min51=%s wmaxOK=%s' %
              (name, s.get('r', float('nan')), s.get('V_minus_R_star', float('nan')),
               s.get('success'), s.get('min_edge_residual_all51'), s.get('widths_max_leq_L')))
    rep['n_below_R_star'] = int(sum(1 for s in rep['runs'] if s.get('below_R_star')))
    rep['n_below_R_star_feasible'] = int(sum(1 for s in rep['runs']
                                             if s.get('below_R_star_by_1e7_feasible')))
    (OUT / 'near_attack.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
    print('n_below (r<R*) =', rep['n_below_R_star'], ' feasible-below =',
          rep['n_below_R_star_feasible'], '-> near_attack.json')
