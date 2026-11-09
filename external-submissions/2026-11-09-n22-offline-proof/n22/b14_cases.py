"""Enumerate the remaining boundary strips and small cores for b=14."""

from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, product


def canonical(seq):
    return min(s[i:]+s[:i] for s in (seq, seq[::-1]) for i in range(len(s)))


def distributions(total, count):
    if count == 1:
        yield (total,)
    else:
        for n in range(total+1):
            for rest in distributions(total-n, count-1):
                yield (n, *rest)


@dataclass(frozen=True)
class Strip:
    runs: tuple
    ear: int | None
    bridges: tuple
    singles: tuple
    faces: tuple
    ring: tuple
    deep: tuple
    origins: tuple


def make_strip(runs, ear, bridges, singles):
    outer = tuple(i for i in range(14) if i != ear)
    apices = tuple(range(14, 14+len(runs)))
    next_label = 14+len(runs)
    bridge_sites = dict(zip(bridges, range(next_label, next_label+len(bridges))))
    next_label += len(bridges)
    singles_sites = []
    for count in singles:
        singles_sites.append(tuple(range(next_label, next_label+count)))
        next_label += count
    deep = tuple(range(next_label, 22))
    origins = deep + tuple(p for group in singles_sites for p in group)
    if not origins:
        return None

    apex_for_edge = [v for v, run in zip(apices, runs) for _ in range(run)]
    faces = [(p, outer[(j+1) % len(outer)], apex_for_edge[j]) for j, p in enumerate(outer)]
    if ear is not None:
        faces.append((ear-1, ear, (ear+1) % 14))
    ring = []
    boundary_position = 0
    for i, apex in enumerate(apices):
        j = (i+1) % len(apices)
        boundary_position = (boundary_position+runs[i]) % len(outer)
        q = outer[boundary_position]
        ring.append(bridge_sites.get(i, apex))
        ring.extend(singles_sites[i])
        path = [apex]
        if i in bridge_sites:
            path.append(bridge_sites[i])
        path.extend(singles_sites[i])
        if j in bridge_sites:
            path.append(bridge_sites[j])
        path.append(apices[j])
        faces.extend((q, u, v) for u, v in zip(path, path[1:]))

    if len(ring) <= 5 and len(deep) >= 2:
        return None
    neighbors = {p: set() for p in range(14, 22)}
    for face in faces:
        for p in face:
            if p >= 14:
                neighbors[p].update(q for q in face if q < 14)
    blocks = [set((i+j) % 14 for j in range(4)) for i in range(14)]
    if any(not any(ns <= block for block in blocks) for ns in neighbors.values()):
        return None
    return Strip(runs, ear, bridges, singles, tuple(faces), tuple(ring), deep, origins)


def strips(with_ear):
    count = 13 if with_ear else 14
    for n in range(5, 8):
        for runs in product((1, 2, 3), repeat=n):
            if sum(runs) != count or runs != canonical(runs):
                continue
            possible_bridges = tuple(i for i, run in enumerate(runs) if run == 3)
            for bridge_count in range(min(len(possible_bridges), 7-n)+1):
                for bridges in combinations(possible_bridges, bridge_count):
                    for s in range(8-n-bridge_count+1):
                        for singles in distributions(s, n):
                            for ear in (range(1, 14) if with_ear else (None,)):
                                strip = make_strip(runs, ear, bridges, singles)
                                if strip is not None:
                                    yield strip


def edge(a, b):
    return (min(a, b), max(a, b))


@lru_cache(maxsize=None)
def triangulations(cycle, inner, forbidden=frozenset()):
    n = len(cycle)
    if n == 2:
        return ((),) if not inner and edge(*cycle) not in forbidden else ()
    if (n == 3 and inner) or (n <= 5 and len(inner) >= 2):
        return ()
    a, b = cycle[0], cycle[-1]
    root = edge(a, b)
    if root in forbidden:
        return ()
    result = []
    for i in range(1, n-1):
        v = cycle[i]
        if edge(a, v) in forbidden or edge(b, v) in forbidden:
            continue
        for k in range(len(inner)+1):
            left = triangulations(cycle[:i+1], inner[:k], forbidden)
            right = triangulations(cycle[i:], inner[k:], forbidden)
            result.extend(((a, v, b), *f, *g) for f in left for g in right)
    if inner:
        v = inner[0]
        if edge(a, v) not in forbidden and edge(b, v) not in forbidden:
            rest = triangulations((*cycle, v), inner[1:], forbidden | {root})
            result.extend(((a, v, b), *f) for f in rest)
    return tuple(result)


def is_target(strip, core):
    return (strip.ear is None and strip.runs == (2,)*7 and not any(strip.singles)
            and not strip.bridges and len(core) == 7
            and all(strip.deep[0] in face for face in core))


def complete_cases(strip):
    """Discard abstract cores that violate the proved small-cycle constraints."""
    for core in triangulations(strip.ring, strip.deep):
        faces = strip.faces+core
        face_set = {tuple(sorted(face)) for face in faces}
        neighbors = [set() for _ in range(22)]
        marked_apices = set()
        for face in faces:
            outer = tuple(p for p in face if p < 14)
            if len(outer) == 2 and abs(outer[0]-outer[1]) in (1, 13):
                marked_apices.update(p for p in face if p >= 14)
            for p in face:
                neighbors[p].update(q for q in face if q != p)
        if any(not (5 if p in marked_apices else 4) <= len(neighbors[p]) <= 8
               for p in range(14, 22)):
            continue
        if sum(len(neighbors[p]) == 4 for p in range(14, 22)) > 1:
            continue
        if any((p, q, r) not in face_set
               for p in range(22) for q in neighbors[p] if p < q
               for r in neighbors[p] & neighbors[q] if q < r):
            continue
        yield core


if __name__ == '__main__':
    for with_ear in (False, True):
        count, cores, target = 0, 0, 0
        for case in strips(with_ear):
            cores_here = tuple(complete_cases(case))
            count += 1
            cores += len(cores_here)
            target += sum(is_target(case, core) for core in cores_here)
        print(f"ear={with_ear}: {count} strips, {cores} cores, {target} target graph(s)")
