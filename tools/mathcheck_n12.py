"""Portable fresh n=12 root and complete k10 arithmetic replay.

This reimplements the archived integer-rectangle arithmetic, not the
analytic reduction of arbitrary covers. No cached acceptance is read.
The exact root/partition/prunes use Fraction; NumPy int64 accelerates atom
capture after explicit overflow guards. All data paths are repository relative.
"""
from __future__ import annotations
import ast
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as Q
from pathlib import Path
import gzip
import json
import math
import os
import time

DATA = Path(__file__).resolve().parents[1] / "math_data" / "n12"
U = Q("22568935234031792038557518369/62500000000000000000000000000")
CORE = 1 - 2 * U
ROOT = ((Q(1, 20), U), (Q(0), 1-U-Q(1, 20)), (Q(0), 3*U-1))


def require(test, message):
    if not test:
        raise ValueError(message)


class Interval:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = Q(lo), Q(lo if hi is None else hi)
        require(self.lo <= self.hi, "reversed interval")

    def __add__(self, other):
        other = other if isinstance(other, Interval) else Interval(other)
        return Interval(self.lo+other.lo, self.hi+other.hi)
    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -(other if isinstance(other, Interval) else Interval(other))

    def __mul__(self, other):
        other = other if isinstance(other, Interval) else Interval(other)
        v = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(min(v), max(v))
    __rmul__ = __mul__

    def __pow__(self, n):
        require(isinstance(n, int) and n >= 0, "invalid exponent")
        if n == 0:
            return Interval(1)
        v = [self.lo**n, self.hi**n]
        return Interval(0 if n % 2 == 0 and self.lo <= 0 <= self.hi else min(v), max(v))


class Polynomial:
    def __init__(self, value=0):
        self.terms = value if isinstance(value, dict) else {(0, 0, 0, 0): Q(value)}
        self.terms = {k: Q(v) for k, v in self.terms.items() if v}

    def __add__(self, other):
        other = other if isinstance(other, Polynomial) else Polynomial(other)
        terms = self.terms.copy()
        for k, v in other.terms.items():
            terms[k] = terms.get(k, 0)+v
        return Polynomial(terms)
    __radd__ = __add__

    def __neg__(self):
        return Polynomial({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + -(other if isinstance(other, Polynomial) else Polynomial(other))

    def __rsub__(self, other):
        return Polynomial(other) + -self

    def __mul__(self, other):
        other = other if isinstance(other, Polynomial) else Polynomial(other)
        terms = {}
        for a, x in self.terms.items():
            for b, y in other.terms.items():
                k = tuple(i+j for i, j in zip(a, b))
                terms[k] = terms.get(k, 0)+x*y
        return Polynomial(terms)
    __rmul__ = __mul__

    def __truediv__(self, other):
        require(not isinstance(other, Polynomial), "nonconstant polynomial divisor")
        return self * (1/Q(other))

    def __pow__(self, n):
        require(isinstance(n, int) and 0 <= n <= 16, "invalid polynomial degree")
        result = Polynomial(1)
        for _ in range(n):
            result = result*self
        return result

    def derivative(self, i):
        out = {}
        for mon, c in self.terms.items():
            if mon[i]:
                key = tuple(n-(j == i) for j, n in enumerate(mon))
                out[key] = c*mon[i]
        return Polynomial(out)

    def evaluate(self, box):
        result = Interval(0)
        for mon, c in self.terms.items():
            v = Interval(c)
            for x, n in zip(box, mon):
                v = v*x**n
            result = result+v
        return result


VARIABLES = {name: Polynomial({tuple(int(i == j) for j in range(4)): Q(1)})
             for i, name in enumerate(("a", "t", "r", "w"))}


def parse_polynomial(text):
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return Polynomial(node.value)
        if isinstance(node, ast.Name) and node.id in VARIABLES:
            return VARIABLES[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -visit(node.operand)
        if isinstance(node, ast.BinOp):
            a, b = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add): return a+b
            if isinstance(node.op, ast.Sub): return a-b
            if isinstance(node.op, ast.Mult): return a*b
            if isinstance(node.op, ast.Pow) and isinstance(node.right, ast.Constant):
                return a**node.right.value
        raise ValueError("unsupported polynomial syntax")
    return visit(ast.parse(text, mode="eval").body)


def check_root(path):
    doc = json.loads(path.read_text(encoding="utf-8"))
    require(doc["vars"] == ["a", "t", "r", "w"], "incorrect root coordinates")
    a, t, r, w = (VARIABLES[k] for k in doc["vars"])
    b = (1+a+r)/2; s = b*b+w*w/3; aa = 3*b*b-w*w-2*b*w
    derived = [a*a+a*r-a*t-2*r*t+t*t,
               (1+t*t-r*r)*(3*b*b+w*w)-t*(3*b*b-w*w+6*b*w),
               4*w*w-12*r*r+3*(1-a-r)**2,
               w*s*s*(2*a-t+r)*(1-t*t-r*r)+(s-b)*(2*t-2*r-a)*t*t*aa]
    polynomials = [parse_polynomial(p) for p in doc["polynomials"]]
    for actual, expected in zip(polynomials, derived):
        den = math.lcm(*(v.denominator for v in expected.terms.values()))
        require(actual.terms == (expected*den).terms, "root polynomial differs from F,G,H,T")
    require(len(polynomials) == 4, "expected four root equations")
    box = [Interval(*row) for row in doc["box"]]
    require(len(box) == 4 and all(x.lo < x.hi for x in box), "invalid root box")
    center = [Interval((x.lo+x.hi)/2) for x in box]
    y = [[Q(v) for v in row] for row in doc["preconditioner"]]
    require(len(y) == 4 and all(len(row) == 4 for row in y), "invalid root matrix")
    f = [p.evaluate(center) for p in polynomials]
    j = [[p.derivative(k).evaluate(box) for k in range(4)] for p in polynomials]
    error = [[Interval(int(i == k))-sum(y[i][l]*j[l][k] for l in range(4))
              for k in range(4)] for i in range(4)]
    q = max(sum(max(abs(v.lo), abs(v.hi)) for v in row) for row in error)
    require(q < 1, "Krawczyk contraction failed")
    image = [center[i]-sum(y[i][k]*f[k] for k in range(4))
             + sum(error[i][k]*(box[k]-center[k]) for k in range(4)) for i in range(4)]
    require(all(x.lo < z.lo <= z.hi < x.hi for x, z in zip(box, image)), "strict Krawczyk inclusion failed")
    require(0 < box[2].lo < box[2].hi < U, "root radius not below k10 threshold")
    return {"unique_root": True, "strict_self_map": True,
            "contraction_upper": str(q), "radius_interval": [str(box[2].lo), str(box[2].hi)]}


def box(raw):
    require(len(raw) == 3 and all(len(v) == 2 for v in raw), "expected 3D box")
    result = tuple(tuple(Q(x) for x in v) for v in raw)
    require(all(a < b for a, b in result), "degenerate or reversed hub box")
    return result


def check_partition(doc):
    require(not doc["pending"], "pending hub boxes remain")
    root = box(doc["domain"])
    require(root == ROOT, "incorrect original k10 root domain")
    trie = {}; counts = {"atomic": 0, "infeasible": 0}
    for leaf in doc["leaves"]:
        require(leaf["type"] in counts, "unknown leaf type")
        counts[leaf["type"]] += 1
        target = box(leaf["H"]); current = root; node = trie
        for _ in range(401):
            require(all(a <= c < d <= b for (a, b), (c, d) in zip(current, target)), "box outside root")
            if current == target:
                require(not node, "duplicate or overlapping frontier")
                node["end"] = True
                break
            require("end" not in node, "overlapping ancestor leaf")
            widths = [b-a for a, b in current]; k = widths.index(max(widths))
            a, b = current[k]; m = (a+b)/2
            if target[k][1] <= m: bit, pair = 0, (a, m)
            elif target[k][0] >= m: bit, pair = 1, (m, b)
            else: raise ValueError("frontier crosses a canonical split")
            node = node.setdefault(bit, {}); current = tuple(pair if i == k else v for i, v in enumerate(current))
        else: raise ValueError("hub partition depth exceeded")
    stack = [trie]; internal = 0
    while stack:
        node = stack.pop()
        if "end" in node: require(set(node) == {"end"}, "nonterminal leaf")
        else:
            require(set(node) == {0, 1}, "coverage gap in binary partition")
            internal += 1; stack.extend((node[0], node[1]))
    require(counts == {"atomic": 6723, "infeasible": 318} and internal == 7040, "incorrect terminal count")
    return {**counts, "internal_nodes": internal, "closed_root_partition": True}


def square_lower(lo, hi):
    return 0 if lo <= 0 <= hi else min(lo*lo, hi*hi)


def check_prunes(doc, core_points):
    points = [(Q(x), Q(y)) for x, y in core_points]
    require(points and all(x*x+y*y == CORE*CORE for x, y in points), "invalid exact core witness")
    counts = {}
    for leaf in doc["leaves"]:
        if leaf["type"] != "infeasible": continue
        (sl, sh), (xl, xh), (yl, yh) = box(leaf["H"])
        reason = None
        if square_lower(xl+sl, xh+sh)+square_lower(yl, yh) > (1-U)**2:
            reason = "outer hub inactive"
        elif any(min(square_lower(xl-sh-cx, xh-sl-cx)+square_lower(yl-cy, yh-cy),
                     square_lower(xl+sl-cx, xh+sh-cx)+square_lower(yl-cy, yh-cy)) > U*U for cx, cy in points):
            reason = "rational core witness"
        elif xh < CORE:
            q2 = CORE*CORE-xh*xh; rhs = U*U-sl*sl-yl*yl-q2
            if rhs < 0 or 4*yl*yl*q2 > rhs*rhs:
                reason = "core bisector endpoints"
                k = math.isqrt((q2.numerator << 200)//q2.denominator)
                lower = Q(k, 1 << 100)
                require(sl*sl+(yl+lower)**2 > U*U, "radical crosscheck failed")
        require(reason is not None, "unproved infeasible leaf")
        counts[reason] = counts.get(reason, 0)+1
    require(sum(counts.values()) == 318, "missing prune")
    return counts


_VECTORS = {}


def init_worker(data):
    global _VECTORS
    _VECTORS = {}
    for n in (2048, 8192):
        v = json.loads((Path(data)/f"vectors-{n}.json").read_text(encoding="utf-8"))
        v = v["vectors"] if isinstance(v, dict) else v
        units = [(Q(c), Q(s)) for c, s in v]
        require(len(units) == n and all(c*c+s*s == 1 for c, s in units), "invalid unit vector set")
        _VECTORS[n] = units


def atomic_replay(item):
    import numpy as np
    idx, leaf, scale = item
    require(type(scale) is int and scale in (26, 28), "unsupported scale")
    n = leaf.get("atomN", 2048)
    require(n in (2048, 8192), "unsupported atom count")
    (sl, sh), (xl, xh), (yl, yh) = box(leaf["H"])
    require(all(a <= c < d <= b for (a, b), (c, d) in zip(ROOT, box(leaf["H"]))), "atomic box outside domain")
    weights = [[Q(v) for v in row] for row in leaf["proposal"]["weights"]]
    require(len(weights) == 3 and len({len(w) for w in weights}) == 1
            and len(weights[0]) >= 5 and len(weights[0]) % 2 == 1, "invalid weight polynomial")
    order = (len(weights[0])-1)//2; S = 1 << scale; rectangles = []; demand = []
    floor = lambda x: x.numerator//x.denominator
    ceil = lambda x: -((-x.numerator)//x.denominator)
    for j, row in enumerate(weights):
        for c, s in _VECTORS[n]:
            if j == 1 and U*c > sl or j == 2 and U*c < -sl: continue
            v, co, si = row[0], Q(1), Q(0)
            for k in range(1, order+1):
                co, si = co*c-si*s, si*c+co*s
                v += row[k]*co+row[order+k]*si
            require(v >= 0, "negative atom density")
            wt = round(v*10**9)
            if not wt: continue
            if j == 0: rx, ry = (c, c), (s, s)
            elif j == 1: rx, ry = (xl-sh+U*c, xh-sl+U*c), (yl+U*s, yh+U*s)
            else: rx, ry = (xl+sl+U*c, xh+sh+U*c), (yl+U*s, yh+U*s)
            rectangles.append([floor(rx[0]*S), ceil(rx[1]*S), floor(ry[0]*S), ceil(ry[1]*S)])
            demand.append(wt)
    total = sum(demand)
    require(rectangles and 0 < total < 2**60 and 10*total < 2**63, "invalid demand or overflow")
    require(max(abs(v) for row in rectangles for v in row) <= 2*S and 32*S*S < 2**63, "distance overflow")
    ax0, ax1, ay0, ay1 = np.array(rectangles, dtype=np.int64).T
    wts = np.array(demand, dtype=np.int64)
    u2 = ceil(U*U*S*S); inner = floor((1-U)**2*S*S); outer = ceil((1-U*U)*S*S)
    stack = [(-S, S, -S, S)]; boxes = 0; worst = 0; terminals = 0
    while stack:
        a, b, c, d = stack.pop(); boxes += 1
        require(boxes <= 4_000_000, "ring replay budget exhausted; not certified")
        nearx, neary = max(a, -b, 0), max(c, -d, 0)
        farx, fary = max(abs(a), abs(b)), max(abs(c), abs(d))
        if farx*farx+fary*fary < inner or nearx*nearx+neary*neary > outer:
            terminals += 1; continue
        dx = np.maximum(np.maximum(ax0-b, a-ax1), 0)
        dy = np.maximum(np.maximum(ay0-d, c-ay1), 0)
        captured = int(wts[dx*dx+dy*dy <= u2].sum())
        if 10*captured < total:
            worst = max(worst, captured); terminals += 1; continue
        require(max(b-a, d-c) > 16, "unresolved ring rectangle; not certified")
        if b-a >= d-c:
            require((a+b) % 2 == 0, "nonexact dyadic split")
            m = (a+b)//2; stack.extend([(a, m, c, d), (m, b, c, d)])
        else:
            require((c+d) % 2 == 0, "nonexact dyadic split")
            m = (c+d)//2; stack.extend([(a, b, c, m), (a, b, m, d)])
    require(total-10*worst > 0, "nonstrict atomic inequality")
    return {"idx": idx, "N": n, "scale_exponent": scale, "demand": total,
            "maximum_capture": worst, "gap": total-10*worst, "ring_boxes": boxes, "ring_terminals": terminals}


def run_checks(data_dir=None, workers=4, limit=None, progress=True):
    data = Path(data_dir) if data_dir else DATA
    start = time.monotonic()
    root = check_root(data/"root.json")
    doc = json.loads(gzip.decompress((data/"domain.json.gz").read_bytes()))
    partition = check_partition(doc)
    prunes = check_prunes(doc, json.loads((data/"core-points.json").read_text()))
    atoms = [v for v in doc["leaves"] if v["type"] == "atomic"]
    scales = json.loads((data/"scales.json").read_text())
    require(len(scales) == len(atoms), "scale table incomplete")
    require(limit is None or 0 < limit <= len(atoms), "invalid sample limit")
    selected = atoms if limit is None else atoms[:limit]
    require(type(workers) is int and 1 <= workers <= 64, "invalid worker count")
    tasks = [(i, l, scales[i]) for i, l in enumerate(selected)]
    results = []
    if workers == 1:
        init_worker(data); iterator = map(atomic_replay, tasks)
        for result in iterator:
            results.append(result)
            if progress and (len(results) % 100 == 0 or len(results) == len(tasks)):
                print(f"n12 atomic inequalities: {len(results)}/{len(tasks)} freshly checked", flush=True)
    else:
        with ProcessPoolExecutor(max_workers=workers, initializer=init_worker, initargs=(str(data),)) as pool:
            for result in pool.map(atomic_replay, tasks, chunksize=8):
                results.append(result)
                if progress and (len(results) % 100 == 0 or len(results) == len(tasks)):
                    print(f"n12 atomic inequalities: {len(results)}/{len(tasks)} freshly checked", flush=True)
    require([v["idx"] for v in results] == list(range(len(selected))), "missing or duplicate atomic result")
    full = len(results) == 6723
    return {"n": 12, "scope": "exact root isolation and full k10 branch arithmetic" if full else "exact root, full partition/prunes, sampled k10 atom replay",
            "full_k10_arithmetic": full, "global_optimality_reproved": False,
            "root": root, "partition": partition, "prunes": prunes,
            "fresh_atomic_checks": len(results), "cache_hits": 0,
            "minimum_integer_gap": min(r["gap"] for r in results),
            "ring_boxes_checked": sum(r["ring_boxes"] for r in results),
            "seconds": round(time.monotonic()-start, 3), "atomic_results": results}


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=min(4, os.cpu_count() or 1))
    parser.add_argument("--limit", type=int, help="sample only; never yields a full marker")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    try:
        report = run_checks(workers=args.workers, limit=args.limit)
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
        print("N12 FULL K10 MATH REPLAY PASSED" if report["full_k10_arithmetic"] else "N12 SAMPLED MATH CHECK PASSED (NOT FULL)")
        print(json.dumps({k: v for k, v in report.items() if k != "atomic_results"}, indent=2))
    except (ValueError, OSError, KeyError, TypeError) as error:
        parser.exit(1, f"MATH CHECK FAILED: {error}\n")
