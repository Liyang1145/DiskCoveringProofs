"""Exact LP bounds for finite b=14 incidence cases, with angular subdivision."""

import argparse
from collections import deque
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
import json
from multiprocessing import Pool
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

from b14_cases import complete_cases, is_target, make_strip, strips
from verify import PI, asin, cos, interval, sin, sqrt, square
from verify_b13 import DUAL_SCALE, RADIUS, SCALE, coefficient, direction
from verify_topology import rounded


B = 14
SITES = 22
U = 2*PI/B
LIMIT = 2*asin(RADIUS)
EXCESS = LIMIT-U
ELASTIC = 32


def upper(x):
    return (interval(x).hi*SCALE).__ceil__()


@lru_cache(maxsize=None)
def circle_trig(grid):
    value = Q(grid, SCALE)
    sine = sin(abs(value))
    return (sine if value >= 0 else -sine), cos(abs(value))


def reference_directions():
    dc, ds = rounded(cos(U)), rounded(sin(U))
    c, s = interval(1), interval(0)
    result = []
    for _ in range(B):
        result.append((c, s))
        c, s = rounded(c*dc-s*ds), rounded(s*dc+c*ds)
    return tuple(result)


def angle_extrema():
    total = B*EXCESS
    if not (total-LIMIT).lo > 0 or not (2*LIMIT-total).lo > 0:
        raise ArithmeticError("unexpected angular cap")
    max_abs = Q(0)
    max_square_sum = Q(0)
    for j in range(1, B):
        increments = [EXCESS for _ in range(B)]
        increments[0] -= LIMIT
        increments[j] -= total-LIMIT
        angle = [interval(0)]
        for inc in increments[:-1]:
            angle.append(angle[-1]+inc)
        avg = sum(angle)/B
        values = [a-avg for a in angle]
        max_abs = max(max_abs, max(max(abs(a.lo), abs(a.hi)) for a in values))
        max_square_sum = max(max_square_sum, sum(square(a) for a in values).hi)
    return upper(max_abs), max_square_sum


def add_row(rows, coeff, rhs):
    coeff = tuple(coeff)
    terms = tuple((idx, coefficient(interval(value))) for idx, value in coeff)
    rows.append((terms, upper(rhs)+2*len(terms)))


def arc_tangents():
    refs = [Q(j, 1000) for j in range(0, 251, 10)] + [Q("0.255"), Q("0.256")]
    for x in refs:
        s, c = sin(x), cos(x)
        q = sqrt(RADIUS*RADIUS-square(s))
        d = c-q
        h = x-s*d
        derivative = 1-d*c-d*square(s)/q
        yield derivative/2, h+derivative*(U/2-x)


def sawtooth_cosines():
    values = []
    for i in range(B):
        a = (i-Q(B-1, 2))*EXCESS
        values.append(rounded(cos(a if a.lo >= 0 else -a)))
    return tuple(values)


REF = reference_directions()
PHASE_LIMIT, VARIANCE = angle_extrema()
TANGENTS = tuple(arc_tangents())
SAWTOOTH = sawtooth_cosines()
PATH_LIMITS = {2: LIMIT, 4: 2*asin(2*RADIUS), 6: 2*asin(3*RADIUS)}
SUPPORTS = tuple(direction(np.cos(2*np.pi*j/16), np.sin(2*np.pi*j/16)) for j in range(16))


class ProofLP:
    def __init__(self, faces, origin=None):
        self.edges = [(j, SITES+j) for j in range(B)]
        self.edges += [((j+1) % B, SITES+j) for j in range(B)]
        self.edges += [(p, j) for j, face in enumerate(faces, SITES+B) for p in face]
        self.count = SITES+B+len(faces)
        self.phase = 2*self.count
        self.arc = self.phase+B
        self.t = self.arc+B
        self.slack = self.t+1
        self.rows = []
        self.supports = [set() for _ in self.edges]
        for i in range(len(self.edges)):
            for d in SUPPORTS:
                self.edge_support(i, d)
        if origin is not None:
            for a, b in SUPPORTS:
                self.rows.append((((2*origin, a), (2*origin+1, b), (self.t, -SCALE)), 0))
        self.differences(faces, origin)
        self.arc_area_rows()

    def edge_support(self, i, d):
        a, b = d
        if a*a+b*b > SCALE*SCALE:
            raise ArithmeticError("direction length exceeds one")
        if d in self.supports[i]:
            return False
        self.supports[i].add(d)
        p, q = self.edges[i]
        self.rows.append((((2*p, a), (2*p+1, b), (2*q, -a), (2*q+1, -b), (self.t, -SCALE)), 0))
        return True

    def differences(self, faces, origin):
        network = [[] for _ in range(self.count)]
        for p, q in self.edges:
            network[p].append(q)
            network[q].append(p)
        self.dist = [[0 if i == j else 2*SCALE for j in range(B)] for i in range(B)]

        def constraint(i, j, upper_bound):
            self.dist[i][j] = min(self.dist[i][j], upper(upper_bound))

        for i in range(B):
            next_i = (i+1) % B
            constraint(i, next_i, EXCESS)
            constraint(next_i, i, U)
            distances = {SITES+i: 0}
            queue = deque([SITES+i])
            while queue:
                p = queue.popleft()
                if distances[p] == 6:
                    continue
                for q in network[p]:
                    if q not in distances:
                        distances[q] = distances[p]+1
                        queue.append(q)
            for k in range(1, B//2+1):
                j = (i+k) % B
                length = distances.get(SITES+j)
                if length in PATH_LIMITS:
                    constraint(i, j, PATH_LIMITS[length]-k*U)
        if origin is not None:
            around = {p for face in faces if origin in face for p in face if p < B}
            for p in around:
                constraint((p-1) % B, p, Q(1, 5)-U)
        for k in range(B):
            for i in range(B):
                for j in range(B):
                    self.dist[i][j] = min(self.dist[i][j], self.dist[i][k]+self.dist[k][j])
        for i in range(B):
            for j in range(B):
                if i != j and self.dist[i][j] < 2*SCALE:
                    self.rows.append((((self.phase+i, -SCALE), (self.phase+j, SCALE)), self.dist[i][j]))

    def arc_area_rows(self):
        m = 3*sqrt(3)/4
        g = Q(23057, 50000)
        necessary = PI-RADIUS*RADIUS*(28*m+14*g)
        add_row(self.rows, ((self.arc+i, -1) for i in range(B)), -necessary)
        for i in range(B):
            j = (i+1) % B
            for slope, rhs in TANGENTS:
                add_row(self.rows, ((self.arc+i, 1), (self.phase+i, slope),
                                    (self.phase+j, -slope)), rhs)
        radial = []
        for i, (c, s) in enumerate(REF):
            x = 2*(SITES+i)
            radial.extend(((x, -c), (x+1, -s)))
            values = [SAWTOOTH[(i-j) % B] for j in range(B)]
            mean = sum(values)/B
            coeff = [(x, -c), (x+1, -s)]
            coeff.extend((self.phase+j, (values[(j+1) % B]-values[j])/(B*EXCESS)) for j in range(B))
            add_row(self.rows, coeff, -mean)
        add_row(self.rows, radial, VARIANCE/2-B)

    def tighten(self, box):
        if any(self.dist[i][i] < 0 for i in range(B)):
            return None
        for _ in range(B):
            lo = [max(box[j][0]-self.dist[i][j] for j in range(B)) for i in range(B)]
            hi = [min(box[j][1]+self.dist[j][i] for j in range(B)) for i in range(B)]
            low_sum, high_sum = sum(lo), sum(hi)
            if low_sum > 0 or high_sum < 0 or any(a > b for a, b in zip(lo, hi)):
                return None
            new = tuple((max(a, b-high_sum), min(b, a-low_sum)) for a, b in zip(lo, hi))
            if new == box:
                return box
            box = new
        return box if all(a <= b for a, b in box) else None

    def sector_rows(self, box):
        rows = []
        for i, ((a, b), (c, s)) in enumerate(zip(box, REF)):
            x = 2*(SITES+i)
            ai = self.phase+i
            lo, hi = Q(a, SCALE), Q(b, SCALE)
            sin_a, cos_a = circle_trig(a)
            sin_b, cos_b = circle_trig(b)
            if lo < hi:
                radial_slope = (cos_b-cos_a)/(hi-lo)
                tangent_slope = (sin_b-sin_a)/(hi-lo)
            else:
                radial_slope = tangent_slope = interval(0)
            radial_base = cos_a-radial_slope*lo
            tangent_base = sin_a-tangent_slope*lo
            tangent_error = (hi-lo)**2*max(abs(lo), abs(hi))/8
            add_row(rows, ((x, -c), (x+1, -s), (ai, radial_slope)), -radial_base)
            for sign in (-1, 1):
                add_row(rows, ((x, -sign*s), (x+1, sign*c), (ai, -sign*tangent_slope)),
                        sign*tangent_base+tangent_error)
            mid = (a+b)//2
            sm, cm = circle_trig(mid)
            add_row(rows, ((x, c), (x+1, s), (ai, sm)), cm+sm*Q(mid, SCALE))
        return rows

    def propose(self, rows, bounds):
        ri, ci, values = [], [], []
        for i, (coeff, _) in enumerate(rows):
            for j, v in (*coeff, (self.slack, -SCALE)):
                ri.append(i)
                ci.append(j)
                values.append(v/SCALE)
        matrix = coo_matrix((values, (ri, ci)), shape=(len(rows), self.slack+1)).tocsr()
        rhs = [b/SCALE for _, b in rows]
        obj = np.zeros(self.slack+1)
        obj[self.t], obj[self.slack] = 1, ELASTIC
        eq = np.zeros((1, self.slack+1))
        eq[0, self.phase:self.arc] = 1
        return linprog(obj, A_ub=matrix, b_ub=rhs, A_eq=eq, b_eq=[0],
                       bounds=[(a/SCALE, b/SCALE) for a, b in bounds], method='highs')

    def bound(self, proposal, rows, bounds):
        p = round(float(proposal.eqlin.marginals[0])*DUAL_SCALE)
        residual = [0]*self.phase + [-p*SCALE]*B + [0]*B + [SCALE*DUAL_SCALE, ELASTIC*SCALE*DUAL_SCALE]
        numerator = 0
        for (row, rhs), marginal in zip(rows, proposal.ineqlin.marginals):
            y = max(0, round(-float(marginal)*DUAL_SCALE))
            if y:
                numerator -= y*rhs*SCALE
                for j, value in row:
                    residual[j] += y*value
                residual[self.slack] -= y*SCALE
        numerator += sum(min(r*a, r*b) for r, (a, b) in zip(residual, bounds))
        return Q(numerator, SCALE*SCALE*DUAL_SCALE)

    def node(self, box, rounds):
        local = self.sector_rows(box)
        bounds = [(-SCALE, SCALE)]*self.phase + list(box) + [(0, SCALE)]*(B+1) + [(0, 4*SCALE)]
        bound = Q(0)
        for _ in range(rounds):
            rows = self.rows+local
            lp = self.propose(rows, bounds)
            if not lp.success:
                raise ArithmeticError(lp.message)
            bound = max(bound, self.bound(lp, rows, bounds))
            if bound > RADIUS:
                break
            xy = lp.x[:self.phase].reshape(-1, 2)
            added = False
            for i, (p, q) in enumerate(self.edges):
                vector = xy[p]-xy[q]
                norm = np.linalg.norm(vector)
                if norm > lp.fun+1e-7:
                    added |= self.edge_support(i, direction(*(vector/norm)))
            if not added:
                break
        return bound, lp

    def check(self, node_limit, support_rounds):
        todo = [((-PHASE_LIMIT, PHASE_LIMIT),)*B]
        nodes = 0
        smallest = Q(1)
        while todo and nodes < node_limit:
            box = self.tighten(todo.pop())
            if box is None:
                continue
            bound, lp = self.node(box, support_rounds)
            nodes += 1
            if bound > RADIUS:
                smallest = min(smallest, bound)
                continue
            phase = lp.x[self.phase:self.arc]
            boundary = lp.x[2*SITES:2*(SITES+B)].reshape(-1, 2)
            basis = np.array([[float(c.lo), float(s.lo)] for c, s in REF])
            radial_gap = np.maximum(0, np.cos(phase)-(boundary*basis).sum(1))
            scores = [(b-a)*(0.004+radial_gap[i]) if b-a >= 2 else 0 for i, (a, b) in enumerate(box)]
            i = int(np.argmax(scores))
            a, b = box[i]
            if b-a < 2:
                return False, nodes, bound
            mid = (a+b)//2
            left = box[:i]+((a, mid),)+box[i+1:]
            right = box[:i]+((mid, b),)+box[i+1:]
            if phase[i]*SCALE <= mid:
                todo.extend((right, left))
            else:
                todo.extend((left, right))
        return not todo, nodes, smallest


def pilot(nodes):
    strip = make_strip((2,)*7, None, (), (0,)*7)
    counts = [0, 0]
    for degree in (6, 5, 4):
        for neighbors in combinations(strip.ring, degree):
            v = strip.deep[0]
            core = tuple((v, p, neighbors[(i+1) % degree]) for i, p in enumerate(neighbors))
            ok, used, margin = ProofLP(strip.faces+core, v).check(nodes, 6)
            counts[0 if ok else 1] += 1
            print(degree, neighbors, ok, used, float(margin) if ok else None, flush=True)
    strip = make_strip((2,)*7, None, (), (1,0,0,0,0,0,0))
    for core in complete_cases(strip):
        ok, _, _ = ProofLP(strip.faces+core, strip.origins[0]).check(nodes, 5)
        counts[0 if ok else 1] += 1
    print('all length-two runs, one deep site:', counts, flush=True)
    if counts[1]:
        raise ArithmeticError('Uncertified length-two case')


def certify_strip(args):
    index, strip, nodes = args
    cores = tuple(core for core in complete_cases(strip) if not is_target(strip, core))
    total = len(cores)*len(strip.origins)
    if not total or ProofLP(strip.faces).check(1, 3)[0]:
        return {'index': index, 'total': total, 'open': []}
    unproved = []
    for origin in strip.origins:
        if ProofLP(strip.faces, origin).check(1, 3)[0]:
            continue
        groups = {}
        for core in cores:
            star = tuple(sorted(tuple(sorted(f)) for f in core if origin in f))
            groups.setdefault(star, []).append(core)
        for star, group in groups.items():
            if star and len(group) > 1 and ProofLP(strip.faces+star, origin).check(1, 3)[0]:
                continue
            for core in group:
                ok, used, _ = ProofLP(strip.faces+core, origin).check(nodes, 4)
                if not ok:
                    unproved.append({'core': core, 'origin': origin, 'nodes': used})
    return {'index': index, 'total': total, 'open': unproved}


def batch(ear, start, count, nodes, workers, log):
    end = None if count is None else start+count
    cases = ((i, st, nodes) for i, st in enumerate(strips(ear))
             if i >= start and (end is None or i < end))

    def report(results):
        verified = 0
        remaining = 0
        strips_seen = 0
        for item in results:
            item['ear'] = ear
            verified += item['total']-len(item['open'])
            remaining += len(item['open'])
            strips_seen += 1
            line = json.dumps(item, separators=(',', ':'))
            if log:
                with log.open('a', encoding='utf-8') as handle:
                    handle.write(line+'\n')
            if not log or item['open'] or strips_seen % 100 == 0:
                print(line, flush=True)
        print(f'ear={ear}: {strips_seen} strips, {verified} exact exclusions, {remaining} open', flush=True)
        return remaining

    if workers == 1:
        return report(map(certify_strip, cases))
    with Pool(workers) as pool:
        return report(pool.imap_unordered(certify_strip, cases, chunksize=1))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--nodes', type=int, default=64)
    parser.add_argument('--pilot', action='store_true')
    parser.add_argument('--ear', action='store_true')
    parser.add_argument('--start', type=int, default=0)
    parser.add_argument('--count', type=int, default=1)
    parser.add_argument('--all', action='store_true')
    parser.add_argument('--workers', type=int, default=1)
    parser.add_argument('--log', type=Path)
    args = parser.parse_args()
    if args.pilot:
        pilot(args.nodes)
        return
    families = (False, True) if args.all else (args.ear,)
    count = None if args.all else args.count
    open_count = sum(batch(ear, args.start, count, args.nodes, args.workers, args.log) for ear in families)
    if open_count:
        raise ArithmeticError(f'{open_count} incidence cases still open')


if __name__ == '__main__':
    main()
