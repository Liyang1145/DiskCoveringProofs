"""Branch-and-bound driver: fresh per-(sub)box fitted energy certificates for
root25 OPEN boxes (no-origin 134-rod model; stronger than either origin branch).
Output: certs/<index>.json with a split tree; leaves carry integer weight
numerators (denominator 10^12) and the claimed rigorous margin (re-checked
independently by verify_certs.py)."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json, os, sys, time
from fractions import Fraction as F
import numpy as np
from scipy.optimize import minimize
import certify_box as cb
import diag_open as dg

DEN = 10 ** 12
d = json.load(open(DCP_N26+'/pending.json'))
BOX = {b['index']: b for b in d['pending_closed_leaf_boxes']}
DIAG = {r['index']: r for r in json.load(open(DCP_N26+'/diag_merged.json'))}
os.makedirs(DCP_N26+'/certs', exist_ok=True)


def worst_point(lo, hi):
    lof = np.array([float(x) for x in lo]); hif = np.array([float(x) for x in hi])
    best = None
    for th0 in [(lof + hif) / 2]:
        t, viol, z = dg.solve(lof, hif, None, th0)
        if viol < 1e-9 and (best is None or t < best[0]): best = (t, z[:15])
    return best


DEADLINE = float(os.environ.get('DEADLINE', '1e18'))


def certify(idx, max_nodes=600, tlimit=float(os.environ.get('TLIMIT','45'))):
    tlimit = min(tlimit, DEADLINE - time.time())
    if tlimit < 5:
        return idx, 'skipped'
    b = BOX[idx]
    lo0 = [F(x) for x in b['lower']]; hi0 = [F(x) for x in b['upper']]
    th = np.array(DIAG[idx]['None'][1])
    lam, _ = cb.fit_weights(th)
    w0 = [int(x * DEN) for x in cb.rationalize_weights(lam, den=DEN)]
    cache = {}
    def kern(wn):
        key = tuple(wn)
        if key not in cache:
            cache[key] = cb.exact_pairs([F(x, DEN) for x in wn])
        return cache[key]
    t0 = time.time(); nodes = 0
    def rec(lo, hi, wn, depth):
        nonlocal nodes
        nodes += 1
        if nodes > max_nodes or time.time() - t0 > tlimit:
            return {'kind': 'OPEN', 'reason': 'budget'}
        pairs, W = kern(wn)
        bd, st = cb.box_bound(pairs, W, lo, hi)
        if bd is not None and bd > 0:
            return {'kind': 'LEAF', 'w': wn, 'margin_over_W': str(bd / W)}
        wp = worst_point(lo, hi)
        if wp is not None:
            if wp[0] <= float(cb.RSTAR_UP) + 1e-12:
                return {'kind': 'OPEN', 'reason': 'model-min<=R* (%.3e)' % (wp[0] - float(cb.RSTAR_UP)), 'theta': list(map(float, wp[1]))}
            lam, _ = cb.fit_weights(wp[1])
            wn2 = [int(x * DEN) for x in cb.rationalize_weights(lam, den=DEN)]
            pairs2, W2 = kern(wn2)
            bd2, st2 = cb.box_bound(pairs2, W2, lo, hi)
            if bd2 is not None and bd2 > 0:
                return {'kind': 'LEAF', 'w': wn2, 'margin_over_W': str(bd2 / W2)}
            wn = wn2
        if depth >= 14:
            return {'kind': 'OPEN', 'reason': 'depth'}
        r = [h - l for l, h in zip(lo, hi)]
        ax = max(range(15), key=lambda k: r[k])
        mid = (lo[ax] + hi[ax]) / 2
        hl = list(hi); hl[ax] = mid
        lr = list(lo); lr[ax] = mid
        return {'kind': 'SPLIT', 'axis': ax, 'mid': str(mid),
                'children': [rec(lo, hl, wn, depth + 1), rec(lr, hi, wn, depth + 1)]}
    tree = rec(lo0, hi0, w0, 0)
    def count(t, k):
        if t['kind'] == 'SPLIT': return sum(count(c, k) for c in t['children'])
        return 1 if t['kind'] == k else 0
    out = {'index': idx, 'lower': b['lower'], 'upper': b['upper'], 'weight_den': DEN,
           'tree': tree, 'leaves': count(tree, 'LEAF'), 'open': count(tree, 'OPEN'),
           'nodes': nodes, 'seconds': time.time() - t0}
    if out['open'] and any(True for _ in [0]) and time.time() - t0 >= tlimit - 1:
        out['budget_hit'] = True
    tmp = DCP_N26+'/certs/.%d.tmp' % idx
    json.dump(out, open(tmp, 'w')); os.replace(tmp, DCP_N26+'/certs/%d.json' % idx)
    return idx, out['leaves'], out['open'], nodes, round(out['seconds'], 1)


if __name__ == '__main__':
    from multiprocessing import Pool
    done = {int(f[:-5]) for f in os.listdir(DCP_N26+'/certs') if f.endswith('.json')}
    order = sorted(BOX, key=lambda i: -DIAG[i]['None'][0])  # easiest first
    todo = [i for i in order if i not in done]
    if len(sys.argv) > 1 and sys.argv[1] == 'hard':
        todo = todo[::-1]
    print('todo', len(todo), flush=True)
    with Pool(2) as p:
        for r in p.imap_unordered(certify, todo, chunksize=1):
            print(r, flush=True)
