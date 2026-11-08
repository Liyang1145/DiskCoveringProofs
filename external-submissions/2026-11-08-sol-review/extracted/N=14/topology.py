"""Radial inequalities and finite face lists for the Voronoi reduction."""

from collections import Counter

from interval import Interval as I, PI, asin
from lower import ends, outer_domain, radial_max, ten_arcs_three_marks, verify_boxes
from upper import ROOT_R


def compositions(total, length):
    if length == 1:
        yield (total,)
        return
    for part in range(total+1):
        for tail in compositions(total-part, length-1):
            yield (part,)+tail


def collar_faces(boundary, walk, core):
    """Place the successive steps of an inner boundary walk at outer vertices."""
    length = len(walk)
    for sizes in compositions(length, len(boundary)):
        for start in range(length):
            faces = list(core)
            position = start
            for j, (outer, size) in enumerate(zip(boundary, sizes)):
                path = [walk[(position+i) % length] for i in range(size+1)]
                if len(set(path)) != len(path):
                    break
                faces.extend((outer, b, a) for a, b in zip(path, path[1:]))
                faces.append((outer, boundary[(j+1) % len(boundary)], path[-1]))
                position += size
            else:
                yield tuple(faces)


def face_lists(n):
    """Generate an exhaustive labeled list, with repetitions allowed."""
    if n == 10:
        boundary = list(range(n))
        for faces in collar_faces(boundary, [10, 11, 12, 13], [(10, 11, 12), (10, 12, 13)]):
            yield "quadrilateral", faces
        for faces in collar_faces(boundary, [10, 11, 12, 10, 13], [(10, 11, 12)]):
            yield "pendant", faces
        return

    assert n == 11
    # Rotate outer labels so vertex 0 is not an ear.
    for mask in range(0, 1 << n, 2):
        if mask & (mask << 1):
            continue
        boundary = [i for i in range(n) if not (mask >> i) & 1]
        ears = tuple(((i-1) % n, i, (i+1) % n) for i in range(n) if (mask >> i) & 1)
        for faces in collar_faces(boundary, [11, 12, 13], [(11, 12, 13)]):
            yield len(ears), faces+ears


def check_face_lists(n):
    totals = Counter()
    for key, faces in face_lists(n):
        totals[key] += 1
        assert len(faces) == 26-n
        assert len({tuple(sorted(face)) for face in faces}) == len(faces)
        assert {v for face in faces for v in face} == set(range(14))
        edges = Counter()
        for a, b, c in faces:
            for u, v in [(a, b), (b, c), (c, a)]:
                edges[u, v] += 1
                edges[v, u] -= 1
        for u in range(n):
            v = (u+1) % n
            edges[u, v] -= 1
            edges[v, u] += 1
        assert all(value == 0 for value in edges.values())
    return dict(sorted(totals.items()))


def main():
    assert __debug__
    r = I(".331733")
    assert (r-ROOT_R).lo > 0
    assert (1-3*r).lo > 0
    bound = I(".726")
    assert (2*PI-14*asin(r)-2*bound).lo > 0
    count = verify_boxes(bound, lambda d: radial_max(I(1), d, r) + asin(r/ends(d)[0]),
                         [outer_domain(r)])
    print("Outer chords spanning >= 2 steps for 10 disks or >= 3 for 11 excluded,",
          count, "boxes.")
    count = ten_arcs_three_marks(r)
    print("10 outer disks and only 3 inner disks adjacent to them excluded,",
          count, "boxes.")
    print("10-outer labeled face lists by inner type:", check_face_lists(10))
    print("11-outer labeled face lists by number of ears:", check_face_lists(11))


if __name__ == "__main__":
    main()
