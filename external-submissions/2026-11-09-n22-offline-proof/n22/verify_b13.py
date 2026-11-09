"""Enumerate the b=13 cases and refute each by an exactly checked LP bound.

SciPy proposes multipliers and support directions. All accepted bounds use
integers and fractions, including the check of each proposed direction.
"""

from fractions import Fraction as Q
from itertools import combinations

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

from verify import PI, asin, cos, interval, sin
from verify_topology import rounded


RADIUS = Q("0.253252")
B = 13
SITES = 22
SCALE = 10**8
DUAL_SCALE = 10**8


def canonical(sequence):
    return min(seq[j:] + seq[:j] for seq in (sequence, sequence[::-1])
               for j in range(len(seq)))


def strips():
    for doubles in combinations(range(8), 5):
        runs = tuple(2 if j in doubles else 1 for j in range(8))
        if runs == canonical(runs):
            yield runs, None
    runs = (1, 2, 2, 2, 2, 2, 2)
    yield runs, None
    for position in range(len(runs)):
        yield runs, position


def outer_faces(runs, extra):
    ring = tuple(range(B, B+len(runs)))
    apices = [site for site, run in zip(ring, runs) for _ in range(run)]
    faces = [(j, (j+1) % B, apices[j]) for j in range(B)]
    for j, site in enumerate(apices):
        previous = apices[j-1]
        if previous != site:
            faces.append((j, previous, site))
    if extra is not None:
        j = sum(runs[:extra+1]) % B
        left, right = ring[extra], ring[(extra+1) % len(ring)]
        site = B+len(ring)
        faces.remove((j, left, right))
        faces.extend(((j, left, site), (j, site, right)))
        ring = (*ring[:extra+1], site, *ring[extra+1:])
    return tuple(faces), ring


def core_cases(ring):
    if len(ring) == 8:
        origin = 21
        for degree in range(5, 9):
            for neighbors in combinations(ring, degree):
                yield tuple((origin, site, neighbors[(i+1) % degree])
                            for i, site in enumerate(neighbors))
        return

    if len(ring) != 7:
        raise ValueError("unexpected core boundary size")
    p, q = 20, 21
    for ear in (None, *range(7)):
        if ear is None:
            core = ring
            ear_faces = ()
        else:
            core = ring[:ear] + ring[ear+1:]
            ear_faces = ((ring[ear-1], ring[ear], ring[(ear+1) % 7]),)
        length = len(core)
        for start in range(length):
            cycle = core[start:] + core[:start]
            for first_run in range(3, length-2):
                faces = [(p, q, cycle[0]), (p, q, cycle[first_run])]
                for i, site in enumerate(cycle):
                    apex = p if i < first_run else q
                    faces.append((apex, site, cycle[(i+1) % length]))
                yield (*ear_faces, *faces)


def coefficient(x):
    value = (x.lo*SCALE).__floor__()
    if x.hi*SCALE > value+2:
        raise ArithmeticError("coefficient interval too wide")
    return value


def boundary_rows():
    """Valid integer-coefficient rows for the rotated boundary points."""
    unit_angle = 2*PI/B
    excess = 2*asin(RADIUS)-unit_angle
    spread = excess*((B-1)//2)
    error = (spread*spread*spread/6).hi
    tangent_slack = (error*SCALE).__ceil__()+6
    step_c, step_s = rounded(cos(unit_angle)), rounded(sin(unit_angle))
    c, s = interval(1), interval(0)
    for i in range(B):
        x = 2*(SITES+i)
        qc, qs = coefficient(c), coefficient(s)
        eps = [((i-j) % B - (B-1)//2)*excess for j in range(B)]
        radial = tuple((cos(e if e.lo >= 0 else -e).lo*SCALE).__floor__() for e in eps)
        tangent = tuple(coefficient(e) for e in eps)
        yield x, ((x, -qc), (x+1, -qs)), radial, 4
        for sign in (-1, 1):
            pair = ((x, -sign*qs), (x+1, sign*qc))
            yield x, pair, tuple(-sign*t for t in tangent), tangent_slack
        c, s = rounded(c*step_c-s*step_s), rounded(s*step_c+c*step_s)


def direction(x, y):
    p, q = int(x*SCALE), int(y*SCALE)
    while p*p+q*q > SCALE*SCALE:
        if abs(p) >= abs(q):
            p -= 1 if p > 0 else -1
        else:
            q -= 1 if q > 0 else -1
    return p, q


class Relaxation:
    def __init__(self, faces, arc_rows):
        count = SITES+B+len(faces)
        self.edges = [(i, SITES+i) for i in range(B)]
        self.edges += [((i+1) % B, SITES+i) for i in range(B)]
        self.edges += [(i, j) for j, face in enumerate(faces, SITES+B) for i in face]
        self.lam = 2*count
        self.t = self.lam+B
        self.rows = []
        for _, pair, coeff, rhs in arc_rows:
            self.rows.append((pair + tuple((self.lam+j, v) for j, v in enumerate(coeff)), rhs))
        self.directions = [set() for _ in self.edges]
        for j in range(16):
            angle = 2*np.pi*j/16
            step = direction(np.cos(angle), np.sin(angle))
            for i in range(len(self.edges)):
                self.add_support(i, step)

    def add_support(self, i, step):
        a, b = step
        if a*a+b*b > SCALE*SCALE:
            raise ArithmeticError("support direction norm exceeds one")
        if step in self.directions[i]:
            return False
        self.directions[i].add(step)
        p, q = self.edges[i]
        self.rows.append((((2*p, a), (2*p+1, b), (2*q, -a), (2*q+1, -b), (self.t, -SCALE)), 0))
        return True

    def propose(self):
        ri, ci, values = [], [], []
        for i, (coeff, _) in enumerate(self.rows):
            for j, v in coeff:
                ri.append(i)
                ci.append(j)
                values.append(v/SCALE)
        matrix = coo_matrix((values, (ri, ci)), shape=(len(self.rows), self.t+1)).tocsr()
        rhs = [b/SCALE for _, b in self.rows]
        objective = np.zeros(self.t+1)
        objective[self.t] = 1
        equality = np.zeros((1, self.t+1))
        equality[0, self.lam:self.t] = 1
        box = [(-1, 1)]*self.lam + [(0, 1)]*(B+1)
        return linprog(objective, A_ub=matrix, b_ub=rhs, A_eq=equality,
                       b_eq=[1], bounds=box, method="highs")

    def exact_bound(self, proposal):
        p = round(float(proposal.eqlin.marginals[0])*DUAL_SCALE)
        residual = [0]*self.lam + [-p*SCALE]*B + [SCALE*DUAL_SCALE]
        numerator = p*SCALE
        for (row, rhs), marginal in zip(self.rows, proposal.ineqlin.marginals):
            y = max(0, round(-float(marginal)*DUAL_SCALE))
            if y:
                numerator -= y*rhs
                for j, value in row:
                    residual[j] += y*value
        numerator -= sum(abs(x) for x in residual[:self.lam])
        numerator += sum(min(0, x) for x in residual[self.lam:])
        return Q(numerator, SCALE*DUAL_SCALE)

    def certify(self):
        bound = Q(0)
        for _ in range(12):
            proposal = self.propose()
            if not proposal.success:
                raise ArithmeticError(proposal.message)
            bound = max(bound, self.exact_bound(proposal))
            if bound > RADIUS:
                return bound
            xy = proposal.x[:self.lam].reshape(-1, 2)
            added = False
            for i, (p, q) in enumerate(self.edges):
                vector = xy[p]-xy[q]
                length = np.linalg.norm(vector)
                if length > proposal.fun+1e-8:
                    added |= self.add_support(i, direction(*(vector/length)))
            if not added:
                break
        return bound


def check():
    arcs = tuple(boundary_rows())
    count = 0
    lowest = Q(1)
    for runs, extra in strips():
        faces, ring = outer_faces(runs, extra)
        bound = Relaxation(faces, arcs).certify()
        if bound > RADIUS:
            count += 1
            lowest = min(lowest, bound)
            print(runs, extra, "excluded by strip alone", flush=True)
            continue
        core_count = 0
        for core in core_cases(ring):
            bound = Relaxation(faces + core, arcs).certify()
            if bound <= RADIUS:
                raise ArithmeticError(f"uncertified: {runs}, {extra}, {core}, bound {bound}")
            lowest = min(lowest, bound)
            core_count += 1
            count += 1
        print(runs, extra, f"excluded with {core_count} core cases", flush=True)
    print(f"b=13 excluded. {count} exact LP bounds. Smallest certified margin ~ {float(lowest-RADIUS):.7g}")


if __name__ == '__main__':
    check()
