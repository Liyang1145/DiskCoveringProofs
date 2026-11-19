import json
from functools import lru_cache
from itertools import combinations
from pathlib import Path

from graphs import MAIN, boundary_pairs, cases, graph
from intervals import Interval, PI, Q, SCALE, ZERO, cos, sin


CAP = Q(1176,10000)
R = Q(361103,1000000)


def effective(b, n, edges, weights):
    assert len(weights) == len(edges)
    k = [dict() for _ in range(n)]

    def insert(i,j,w):
        assert i != j and w.lo >= 0
        if w.hi:
            k[i][j] = k[j][i] = k[i].get(j,ZERO) + w

    for (i,j),w in zip(edges,weights):
        insert(i,j,w)
    for u in range(n-1,b-1,-1):
        neighbors = list(k[u].items())
        if not neighbors:
            continue
        total = sum(w for _,w in neighbors)
        assert total.lo > 0
        for (i,v),(j,w) in combinations(neighbors,2):
            insert(i,j,v*w/total)
        for i,_ in neighbors:
            del k[i][u]
        k[u].clear()
    return [k[i].get(j,ZERO) for i,j,_ in boundary_pairs(b)]


ANG_SCALE = 10000 * 2**26
ANG_CAP = ANG_SCALE * 1176 // 10000


@lru_cache(maxsize=None)
def affine(left, right, length):
    """Lower affine bound in the sum of the deficits of an arc's gaps."""
    assert 0 <= left <= right <= ANG_CAP*length
    l,r = Q(left,ANG_SCALE), Q(right,ANG_SCALE)
    turn = CAP*length
    if left == right:
        return 2*(1-cos(2*PI*l)), ZERO
    if 4*left >= ANG_SCALE:
        assert 4*right <= 3*ANG_SCALE
        f_l = 2*(1-cos(2*PI*l))
        f_r = 2*(1-cos(2*PI*r))
        slope = (f_r-f_l) / (r-l)
        return f_l + slope*(turn-l), -slope
    middle = Q(right+left,2*ANG_SCALE)
    spread = Q(right-left,2*ANG_SCALE)
    slope = 4*PI*sin(2*PI*middle)
    penalty = ZERO
    if 4*right > ANG_SCALE:
        min_cos = cos(2*PI*r) if 2*right < ANG_SCALE else Q(-1)
        penalty = 4*PI.square()*Interval(min_cos.lo,min_cos.lo)*spread.square()
    return 2*(1-cos(2*PI*middle)) + slope*(turn-middle) + penalty, -slope


def check_case(args, weights):
    b = args[0]
    n,edges = graph(*args)
    assert all(type(w) is int and w >= 0 for w in weights)
    total_weight = sum(weights)
    assert total_weight > 0
    weights = [Q(w,total_weight) for w in weights]
    k = effective(b,n,edges,weights)
    pairs = [(chain,Interval(w.lo,w.lo)) for (_,_,chain),w in zip(boundary_pairs(b),k) if w.lo]

    deficit = ANG_CAP*b-ANG_SCALE
    queue = [((0,)*b, (min(deficit, ANG_CAP),)*b)]
    threshold = R.square().hi*ANG_SCALE
    margin = None
    nodes = 0
    while queue:
        lo,hi = queue.pop()
        nodes += 1
        assert nodes <= 100000
        lower_sum, upper_sum = sum(lo),sum(hi)
        if lower_sum > deficit or upper_sum < deficit:
            continue
        lo = tuple(max(l, deficit-upper_sum+h) for l,h in zip(lo,hi))
        hi = tuple(min(h, deficit-lower_sum+l) for l,h in zip(lo,hi))
        lower_sum, upper_sum = sum(lo),sum(hi)
        grad = [0]*b
        const = 0
        for chain,w in pairs:
            inside_lo,inside_hi = sum(lo[j] for j in chain),sum(hi[j] for j in chain)
            left = len(chain)*ANG_CAP - min(inside_hi, deficit-lower_sum+inside_lo)
            right = len(chain)*ANG_CAP - max(inside_lo, deficit-upper_sum+inside_hi)
            c,a = affine(left,right,len(chain))
            const += (w*c).lo
            lower_slope = (w*a).lo
            for j in chain:
                grad[j] += lower_slope
        lower = const*ANG_SCALE + sum(g*l for g,l in zip(grad,lo))
        remaining = deficit-lower_sum
        for j in sorted(range(b),key=grad.__getitem__):
            applied = min(remaining,hi[j]-lo[j])
            lower += grad[j]*applied
            remaining -= applied
            if remaining == 0:
                break
        assert remaining == 0
        if lower > threshold:
            here = lower-threshold
            margin = here if margin is None else min(here,margin)
            continue
        j = max(range(b),key=lambda i:hi[i]-lo[i])
        if hi[j]-lo[j] <= 1:
            raise AssertionError(f'could not certify graph {args}')
        m = (lo[j]+hi[j])//2
        queue.append((lo,hi[:j]+(m,)+hi[j+1:]))
        queue.append((lo[:j]+(m,)+lo[j+1:],hi))
    assert margin is not None
    return nodes,margin


def replay_networks():
    root = Path(__file__).resolve().parent
    for b in (9,10):
        expected = set(cases(b))-{MAIN}
        loaded = json.loads((root / f'certificate-{b}.json').read_text())
        total_nodes = max_nodes = 0
        smallest = None
        for (number,labels,counts,ears),weights in loaded:
            args = (number,tuple(labels),tuple(counts),tuple(ears))
            expected.remove(args)
            nodes,margin = check_case(args,weights)
            total_nodes += nodes
            max_nodes = max(max_nodes,nodes)
            smallest = margin if smallest is None else min(smallest,margin)
        assert not expected
        print(f'{b} boundary cells: {len(loaded)} cases, {total_nodes} boxes, '
              f'maximum {max_nodes}, floor(10^12 * strict margin) = '
              f'{smallest*10**12//(SCALE*ANG_SCALE)}')
