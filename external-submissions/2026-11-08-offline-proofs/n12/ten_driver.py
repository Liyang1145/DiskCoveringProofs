"""Generate or replay finite certificates for the ten-outer-disk case."""

import argparse
from concurrent.futures import ProcessPoolExecutor
import ctypes as ct
from itertools import count
import json
from math import isqrt
import os
from pathlib import Path
from time import monotonic


S = 1 << 40
R = 397044643907
T = S - 2 * R
Q = 3 * R - S
K = 32
ROOT = ((0, R), (0, (46 * S + 100 * Q + 199) // 200), (0, Q))
ROOT_DIR = Path(__file__).resolve().parent
WEIGHTS = ct.c_int64 * (3 * K)
OUT = ct.c_int64 * 3
LIB = None
SEARCH = None


def load_library():
    global LIB
    if LIB is not None:
        return LIB
    LIB = ct.CDLL(str(ROOT_DIR / os.environ.get('N12_INTERVAL_DLL','ten_intervals.dll')))
    LIB.exposed_half.argtypes = [ct.c_int64, ct.c_int64]
    LIB.exposed_half.restype = ct.c_int64
    LIB.check_measure.argtypes = [ct.c_int64] * 4 + [ct.POINTER(ct.c_int64), ct.c_int64, ct.POINTER(ct.c_int64)]
    LIB.check_measure.restype = ct.c_int
    return LIB


def square_min(lo, hi):
    if lo <= 0 <= hi:
        return 0
    return min(lo * lo, hi * hi)


def prune(box):
    (al, ah), (xl, xh), (yl, yh) = box
    if 10000 * ((al + xl) ** 2 + yl ** 2) >= (46 * S) ** 2:
        return True
    # Exact necessary tests at the bottom intersection of the bisector with
    # the central circle, then its left and right points.
    if xh > T:
        raise ValueError('the bisector must intersect the central disk')
    h = isqrt(T ** 2 - xh ** 2)
    if al ** 2 + (yl + h) ** 2 > R ** 2:
        return True
    if square_min(xl - ah + T, xh - al + T) + yl ** 2 > R ** 2:
        return True
    if square_min(xl + al - T, xh + ah - T) + yl ** 2 > R ** 2:
        return True
    if xl >= ah and (xl-ah) ** 2 + yl ** 2 > Q ** 2:
        return True
    return False


def representative(box):
    centers = [(a+b)//2 for a, b in box]
    ha, hx, hy = [hi - center for (_, hi), center in zip(box, centers)]
    squared = (ha+hx) ** 2 + hy ** 2
    delta = isqrt(squared)
    delta += delta ** 2 < squared
    return (*centers, R + delta)


def split(box):
    i = max(range(len(box)), key=lambda k: box[k][1]-box[k][0])
    lo, hi = box[i]
    mid = (lo+hi)//2
    if lo == mid:
        raise ValueError('no further dyadic split')
    return box[:i] + ((lo, mid),) + box[i+1:], box[:i] + ((mid, hi),) + box[i+1:]


def check(box, weights, limit=150000):
    if len(weights) != 3*K or any(type(w) is not int or not 0 <= w <= 50000000 for w in weights):
        raise ValueError('weights out of range')
    lib = load_library()
    out = OUT()
    status = lib.check_measure(*representative(box), WEIGHTS(*weights), limit, out)
    return status, tuple(out)


def float_modules():
    global SEARCH
    if SEARCH is None:
        os.environ['OPENBLAS_NUM_THREADS'] = '1'
        import numpy as np
        import ten_search as ts
        samples = ts.grid(45, 160)
        sample_rows = np.arange(len(samples)).reshape((45, 160))[::3, ::2].ravel()
        SEARCH = np, ts, samples, sample_rows
    return SEARCH


def search(box, inherited=None, trial_limit=7):
    lib = load_library()
    a, x, y, rho = representative(box)
    if rho-R > S//42:
        return None, 0, inherited
    np, ts, samples, rows = float_modules()
    exposure = lib.exposed_half(a, rho) / S
    p = (a/S, x/S, y/S, rho/S-ts.R)

    def matrix(radius):
        return ts.measure_matrix(*p, samples, disk_radius=radius, exposure=exposure)

    if inherited is not None:
        mat, mass = matrix(ts.R)
        w = np.array(inherited, dtype=float)
        if (mat @ w).max() < .0992 * (mass @ w):
            status, out = check(box, inherited)
            if status == 1:
                return inherited, out[2], inherited

    # Slightly larger test disks select weights with margin, but the exact
    # check always uses R. The search can only delay or fail certification.
    mat, mass = matrix(ts.R + .00055)
    rows = np.array(rows)
    for attempt in range(trial_limit):
        weights, cap = ts.find_measure(mat[rows], mass)
        if weights is None or cap > .0994:
            break
        scores = mat @ weights
        top = np.argpartition(scores, -120)[-120:]
        if scores[top].max() > .0991 and attempt+1 < trial_limit:
            rows = np.union1d(rows, top)
            continue
        if scores[top].max() >= .1000:
            break
        weights = [min(50000000, int(round(1_000_000 * w))) for w in weights]
        status, out = check(box, weights)
        if status == 1:
            return weights, out[2], weights
        if status == 0:
            new = complex(out[0], out[1])/S
            new_row, _ = ts.measure_matrix(*p, np.array([new]), disk_radius=ts.R + .00055, exposure=exposure)
            rows = np.append(np.union1d(rows, top), len(mat))
            mat = np.vstack([mat, new_row])
            continue
        break
    return None, 0, inherited


def process(item):
    path, box, inherited = item
    if prune(box):
        return path, box, 'prune', 0, None
    weights, checks, warm = search(box, inherited)
    if weights is not None:
        return path, box, weights, checks, warm
    return path, box, None, 0, warm


def generate(file, jobs, depth_limit):
    pending = [('', ROOT, None)]
    verified = pruned = processed = cells = 0
    start = monotonic()
    with file.open('w', encoding='utf-8') as log, ProcessPoolExecutor(max_workers=jobs) as pool:
        for depth in count():
            if not pending or depth > depth_limit:
                break
            following = []
            for path, box, result, checks, warm in pool.map(process, pending):
                processed += 1
                if result is None:
                    for bit, child in enumerate(split(box)):
                        following.append((path+str(bit), child, warm))
                else:
                    log.write(json.dumps([path, result], separators=(',', ':'))+'\n')
                    if result == 'prune':
                        pruned += 1
                    else:
                        verified += 1
                        cells += checks
                if processed % 200 == 0:
                    log.flush()
                    print('depth', depth, 'processed', processed, 'measures', verified,
                          'pruned', pruned, 'outer boxes', cells, 'seconds', round(monotonic()-start, 1), flush=True)
            pending = following
            log.flush()
            print('completed depth', depth, 'next', len(pending), 'measures', verified, 'pruned', pruned,
                  'outer boxes', cells, 'seconds', round(monotonic()-start, 1), flush=True)
    if pending:
        print('INCOMPLETE:', len(pending), 'uncovered boxes', flush=True)
        return False
    print('COMPLETE:', verified, 'measures and', pruned, 'pruned boxes', flush=True)
    return True


def replay(file):
    leaves = {}
    with file.open(encoding='utf-8') as stream:
        for line in stream:
            path, result = json.loads(line)
            if path in leaves or set(path)-set('01') or len(path) > 60:
                raise ValueError('invalid proof tree path')
            leaves[path] = result
    prefixes = {path[:i] for path in leaves for i in range(len(path))}
    pending = [('', ROOT)]
    pruned = verified = cells = 0
    while pending:
        path, box = pending.pop()
        if path not in leaves:
            if path not in prefixes:
                raise ValueError('uncovered proof tree leaf '+path)
            pending.extend((path+str(bit), b) for bit, b in enumerate(split(box)))
            continue
        result = leaves.pop(path)
        if result == 'prune':
            if not prune(box):
                raise ValueError('invalid prune '+path)
            pruned += 1
        else:
            status, out = check(box, result)
            if status != 1:
                raise ValueError('invalid measure '+path)
            cells += out[2]
            verified += 1
    if leaves:
        raise ValueError('proof tree has excess leaves')
    print('certified ten boundary disks impossible at', R, '/', S,
          'using', verified, 'measures and', pruned, 'pruned inner boxes;', cells, 'outer boxes')


def main():
    p = argparse.ArgumentParser()
    p.add_argument('action', choices=['generate', 'replay', 'test'])
    p.add_argument('--file', type=Path, default=ROOT_DIR/'ten_certificate.jsonl')
    p.add_argument('--jobs', type=int, default=8)
    p.add_argument('--depth', type=int, default=25)
    args = p.parse_args()
    if args.action == 'generate':
        if not generate(args.file, args.jobs, args.depth):
            raise SystemExit(1)
    elif args.action == 'replay':
        replay(args.file)
    else:
        for a, x, y, width in [(174, 0, 0, 6), (174, 40, 30, 6), (174, 100, 40, 12),
                                (200, 0, 20, 6), (140, 130, 40, 12), (60, 60, 60, 20)]:
            half = width*S//2000
            box = tuple((max(0, v*S//1000-half), v*S//1000+half) for v in (a, x, y))
            start = monotonic()
            weight, cells, _ = search(box)
            print(a, x, y, width, weight is not None, cells, round(monotonic()-start, 3), flush=True)


if __name__ == '__main__':
    main()
