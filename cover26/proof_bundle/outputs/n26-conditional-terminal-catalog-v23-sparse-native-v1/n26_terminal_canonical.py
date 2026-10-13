"""Exact oriented-boundary canonical codes and explicit vertex bijections."""

from collections import defaultdict, deque

from audit_prefix_origin import validate_disk


def image_faces(faces, permutation):
    n = len(permutation)
    if sorted(permutation) != list(range(n)):
        raise ValueError("canonical vertex map is not a bijection")
    return sorted(sum(1 << permutation[i] for i in range(n) if face >> i & 1) for face in faces)


def canonical(n, b, faces):
    validate_disk(n, b, faces)
    triangles = [tuple(i for i in range(n) if face >> i & 1) for face in faces]
    incidence, adjacency = defaultdict(set), [set() for _ in range(n)]
    for k, triangle in enumerate(triangles):
        for u in triangle:
            for v in triangle:
                if u < v:
                    incidence[u, v].add(k)
                    adjacency[u].add(v)
                    adjacency[v].add(u)
    profiles = {(start, direction): [len(adjacency[(start + direction * i) % b]) for i in range(b)]
                for start in range(b) for direction in (-1, 1)}
    minimum = min(profiles.values())
    codes = []
    for (start, direction), profile in profiles.items():
        if profile != minimum:
            continue
        labels = [-1] * n
        for i in range(b):
            labels[(start + direction * i) % b] = i
        end = (start + direction) % b
        root = incidence[tuple(sorted((start, end)))]
        if len(root) != 1:
            raise ValueError("canonical root is not a single boundary triangle")
        first = next(iter(root))
        seen, queue, next_label = {first}, deque([(first, start, end)]), b
        while queue:
            k, u, v = queue.popleft()
            third = set(triangles[k]) - {u, v}
            if len(third) != 1 or labels[u] < 0 or labels[v] < 0:
                raise ValueError("invalid rooted dual traversal")
            w = next(iter(third))
            if labels[w] < 0:
                labels[w] = next_label
                next_label += 1
            for a, c in ((v, w), (w, u)):
                unseen = incidence[tuple(sorted((a, c)))] - seen
                if unseen:
                    if len(unseen) != 1:
                        raise ValueError("nonmanifold dual traversal")
                    other = next(iter(unseen))
                    seen.add(other)
                    queue.append((other, a, c))
        if len(seen) != len(faces) or next_label != n:
            raise ValueError("canonical traversal omitted a face or vertex")
        code = image_faces(faces, labels)
        codes.append({"faces": code, "vertex_to_canonical": labels,
                      "boundary_start": start, "boundary_direction": direction})
    best = min(row["faces"] for row in codes)
    maps = [row for row in codes if row["faces"] == best]
    return {"faces": best, "stabilizer": len(maps), "minimum_boundary_degree_profile": minimum,
            "canonical_bijections": maps}


def check_bijection(n, b, faces, code, mapping):
    labels, start, direction = (mapping["vertex_to_canonical"],
                                mapping["boundary_start"], mapping["boundary_direction"])
    if (type(start) is not int or not 0 <= start < b or direction not in (-1, 1)
            or len(labels) != n or sorted(labels) != list(range(n))
            or any(labels[(start + direction * i) % b] != i for i in range(b))
            or any(labels[i] < b for i in range(b, n)) or image_faces(faces, labels) != code):
        raise ValueError("stored canonical map does not preserve boundary and every face")
