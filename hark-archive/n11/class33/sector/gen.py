"""Adaptive sector tree generator (exact Fractions), resumable.  usage: gen.py <tag> <sector i> [budget_s]
State file data/sector_<tag>_<i>.state.json = {M, tokens(pre-order, done so far), stack(pending boxes)}.
Tokens: ['S',dim,t] | ['L',cl,ch,hl,hh]  (Fractions as 'n/d')."""
import json, os, sys, time
from fractions import Fraction as F
from kernel import *
D = '/workspace/work/dcp-n11-lean/class33/data/'
def fs(x): return f'{x.numerator}/{x.denominator}'
def wr(p, obj):
    t = p + '.tmp'; open(t, 'w').write(json.dumps(obj)); os.replace(t, p)
def nice_split(lo, hi):
    mid = (lo + hi) / 2; w = hi - lo
    k = 0
    while True:
        N = 1 << k
        t = F(round(mid * N), N)
        if lo < t < hi and abs(t - mid) <= w / 4: return t
        k += 1
def coeffs(tag, i):
    d = json.load(open(D + {'q0m2': 'q0_m2.json', 'rep7': 'rep_k7.json', 'rep1': 'rep_k1.json'}[tag]))
    s = d['sectors'][str(i)]
    return tuple(F(s[k]) for k in ('C', 'mu', 'dL', 'dR', 'bL', 'bR'))
def box_of(b): return tuple((F(x), F(y)) for x, y in b)
def run(tag, i, M, budget, P=20, minw=F(1, 10**6)):
    co = coeffs(tag, i)
    sp = D + f'sector_{tag}_{i}.state.json'
    if os.path.exists(sp):
        st = json.load(open(sp))
        M = F(st['M'])
        stack = [[(F(x), F(y)) for x, y in b] for b in st['stack']]; toks = st['tokens']
    else:
        stack = [[(F(0), PIHI), (F(0), F(1)), (F(0), F(1))]]; toks = []
    t0 = time.time(); n = 0
    def save(done=False):
        wr(sp, dict(M=fs(M), tokens=toks, stack=[[[fs(x), fs(y)] for x, y in b] for b in stack], done=done))
    while stack:
        if time.time() - t0 > budget: save(); return False, len(toks)
        B = tuple(stack.pop()); n += 1
        b, K = leafBound(co, B, P)
        if b is not None and b <= M:
            toks.append(['L'] + [fs(x) for x in K]); continue
        # choose split dim: minimize max child bound
        best = None
        for dim in range(3):
            lo, hi = B[dim]
            if hi - lo < minw: continue
            t = nice_split(lo, hi)
            L = list(B); R = list(B); L[dim] = (lo, t); R[dim] = (t, hi)
            bl, _ = leafBound(co, tuple(L), P); br, _ = leafBound(co, tuple(R), P)
            if bl is None or br is None: continue
            sc = bl + br
            if best is None or sc < best[0]: best = (sc, dim, t, L, R)
        if best is None:
            save(); raise RuntimeError(f'stuck at {B} bound {b}')
        _, dim, t, L, R = best
        toks.append(['S', dim, fs(t)])
        stack.append(list(R)); stack.append(list(L))
    save(True); return True, len(toks)
if __name__ == '__main__':
    tag = sys.argv[1]; i = int(sys.argv[2]); budget = float(sys.argv[3]) if len(sys.argv) > 3 else 90
    M = F(sys.argv[4]) if len(sys.argv) > 4 else None
    print(run(tag, i, M, budget))
