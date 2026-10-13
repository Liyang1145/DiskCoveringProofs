"""Stdlib-only root-open-edge filling; supports pinched pure inner frontiers."""
from collections import defaultdict
from itertools import combinations
from complete_simple_collar import bits, simple_holes
from cross_order_strict_transfer import validate_disk

assert __debug__


def start_states(N, B, centers, outer):
    assert N == 25 and B in (14, 15, 16, 17)
    assert B <= centers <= N and outer == sorted(set(outer)) and outer
    assert all(mask & ((1 << B)-1) for mask in outer)
    try:
        simple_holes(centers, B, outer)
    except AssertionError as error:
        # The only newly handled initial condition: simple_holes has already
        # checked edge incidence, orientation, face-dual connection and outer
        # orientation before it reaches this specific failed test.
        assert str(error) == "pinched hole boundary", "general filling source outside accepted collar domain"
    used = 0
    for mask in outer:
        assert 0 < mask < 1 << centers and mask.bit_count() == 3
        used |= mask
    assert used == (1 << centers)-1
    return [{"faces": list(outer), "next": centers, "pending": []}]


def children(state, N, B):
    faces, next_label = state["faces"], state["next"]
    assert state["pending"] == [] and faces == sorted(set(faces))
    assert B <= next_label <= N
    assert all(0 < mask < 1 << next_label and mask.bit_count() == 3 for mask in faces)
    target = 2*N-B-2
    assert len(faces) <= target
    if len(faces) == target:
        if next_label != N:
            return []
        try:
            validate_disk(N, B, faces)
        except AssertionError:
            return []
        return None
    incidence = defaultdict(int)
    for mask in faces:
        for edge in combinations(bits(mask), 2):
            incidence[edge] += 1
    assert all(count <= 2 for count in incidence.values())
    exterior = {tuple(sorted((v, (v+1) % B))) for v in range(B)}
    assert all(incidence[edge] == 1 for edge in exterior)
    frontier = sorted(edge for edge, count in incidence.items() if count == 1 and edge not in exterior)
    if not frontier:
        # A connected full disk's face dual cannot add a new face component
        # without an open non-exterior edge in the existing connected faces.
        return []
    a, c = frontier[0]
    if a < B or c < B:
        # Complete saturated outer fans cannot receive further B faces.
        return []
    result = []
    for w in range(B, next_label+(next_label < N)):
        if w in (a, c):
            continue
        mask = (1 << a) | (1 << c) | (1 << w)
        if mask in faces:
            continue
        if incidence[tuple(sorted((a, w)))] >= 2 or incidence[tuple(sorted((c, w)))] >= 2:
            continue
        result.append({"faces": sorted(faces+[mask]),
                       "next": next_label+(w == next_label), "pending": []})
    return result
