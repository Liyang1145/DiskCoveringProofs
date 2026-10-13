"""Exact rational box utilities for n12 domain sharding.

A box is B = ((s_lo,s_hi),(x_lo,x_hi),(y_lo,y_hi)) with Fraction endpoints.
JSON form (matching lead/hubline_domain.py's `encode`): [[str,str],[str,str],
[str,str]] where each str is an exact Fraction literal such as "3/40".

Canonical refinement MUST match lead/hubline_domain.py:
    k = max(range(3), key=lambda j: widths[j])       # first maximal index
    m = (lo+hi)/2 ;  children (lo,m),(m,h)  in dimension k
Python's max returns the first index attaining the maximum, which pins the
tie-break to the smallest index; this module reproduces exactly that rule.
"""
import hashlib
import json
from fractions import Fraction as F

DIMS = 3


# --------------------------------------------------------------- encoding
def decode(H):
    return tuple(tuple(F(v) for v in row) for row in H)


def encode(B):
    return [[str(lo), str(hi)] for lo, hi in B]


def box_str(B):
    """canonical exact string of a box (independent of formatting)."""
    return ";".join("%s,%s" % (lo, hi) for lo, hi in B)


def box_hash(B):
    return hashlib.sha256(box_str(B).encode("ascii")).hexdigest()


def file_sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------- geometry
def widths(B):
    return [hi - lo for lo, hi in B]


def widest_dim(B):
    w = widths(B)
    return max(range(DIMS), key=lambda j: w[j])


def split_box(B):
    k = widest_dim(B)
    lo, hi = B[k]
    m = (lo + hi) / 2
    c1 = list(B); c1[k] = (lo, m)
    c2 = list(B); c2[k] = (m, hi)
    return tuple(c1), tuple(c2)


def contains(A, B):
    """closed-box containment A superset B."""
    return all(A[i][0] <= B[i][0] and B[i][1] <= A[i][1] for i in range(DIMS))


def interiors_overlap(A, B):
    return all(A[i][0] < B[i][1] and B[i][0] < A[i][1] for i in range(DIMS))


def volume(B):
    v = F(1)
    for lo, hi in B:
        v *= (hi - lo)
    return v


def degenerate(B):
    return any(hi == lo for lo, hi in B)


# ------------------------------------------------------------- verification
def check_frontier(root, entries, max_depth=400):
    """entries: iterable of (box, tag).  Verify exactly:
         * every entry is inside root;
         * the canonical widest-dim bisection tree of root, stopped at the
           entries, hits every entry exactly once and covers root;
         * no entry is unused (catches non-canonical or overlapping boxes).
       Returns (ok, reason, stats)."""
    seen = set()
    boxes = {}
    for b, tag in entries:
        k = box_str(b)
        if k in boxes:
            return False, "duplicate box in frontier", {}
        if not contains(root, b):
            return False, "box outside root", {}
        boxes[k] = (b, tag)
    if not boxes:
        return False, "empty frontier", {}

    def rec(B, depth):
        if depth > max_depth:
            return "depth exceeded (canonical tree not reached)"
        k = box_str(B)
        if k in boxes:
            if k in seen:
                return "box visited twice"
            seen.add(k)
            return True
        c1, c2 = split_box(B)
        for c in (c1, c2):
            if not contains(root, c):
                return "child left root"
            r = rec(c, depth + 1)
            if r is not True:
                return r
        return True

    r = rec(root, 0)
    if r is not True:
        return False, str(r), {}
    if len(seen) != len(boxes):
        missing = [boxes[k][0] for k in boxes if k not in seen]
        return False, "unused/overlapping boxes: %d" % len(missing), {}
    stats = dict(n=len(boxes), volume=sum(volume(b) for b, _ in boxes.values()))
    return True, "ok", stats


def check_partition(roots):
    """roots: list of boxes.  Pairwise interior-disjoint required."""
    for i in range(len(roots)):
        for j in range(i + 1, len(roots)):
            if interiors_overlap(roots[i], roots[j]):
                return False, "roots %d and %d overlap" % (i, j)
    return True, "ok"


def check_refinement(parent, children):
    """children must be exactly the two canonical widest-dim halves of parent."""
    c1, c2 = split_box(parent)
    want = sorted([box_str(c1), box_str(c2)])
    got = sorted(box_str(c) for c in children)
    return want == got
