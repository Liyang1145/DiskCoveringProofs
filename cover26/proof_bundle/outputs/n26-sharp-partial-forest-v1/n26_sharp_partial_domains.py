"""Independent sharp necessary domains for introduced partial center complexes."""

from collections import deque

from n26_force import spec_gate
from n26_sharp_radius_constraints import SCALE


def matrix(spec, caps):
    b, n = spec["B"], spec["next"]
    # This gate validates masks and dimensions; rebuild adjacency independently.
    spec_gate(spec)
    adjacency = [set() for _ in range(n)]
    for i in range(b):
        j = (i + 1) % b
        adjacency[i].add(j)
        adjacency[j].add(i)
    for face in spec["faces"]:
        vertices = {i for i in range(n) if face >> i & 1}
        for i in vertices:
            adjacency[i].update(vertices - {i})
    distances = []
    for source in range(n):
        distance, queue = [None] * n, deque([source])
        distance[source] = 0
        while queue:
            u = queue.popleft()
            for v in sorted(adjacency[u]):
                if distance[v] is None:
                    distance[v] = distance[u] + 1
                    queue.append(v)
        if any(value is None for value in distance):
            raise ValueError("introduced partial center complex is disconnected")
        distances.append(distance)
    edges = {}

    def edge(i, j, bound):
        edges[i, j] = min(edges.get((i, j), 2 * SCALE), bound)

    for i in range(b):
        j = (i + 1) % b
        edge(i, j, caps[0] - int(j == 0) * SCALE)
        edge(j, i, int(j == 0) * SCALE)
    witnesses = []
    for i in range(b):
        for j in range(i + 1, b):
            h = min(distances[u][v] for u in (i, (i + 1) % b)
                    for v in (j, (j + 1) % b))
            steps = j - i
            if h > 3 or min(steps, b - steps) * caps[0] <= caps[h]:
                continue
            forward = steps * caps[0] < SCALE - caps[h]
            backward = (b - steps) * caps[0] < SCALE - caps[h]
            witnesses.append({"anchors": [i, j], "center_path_edges": h,
                              "forward_forced_short": forward, "backward_forced_short": backward})
            if forward and backward:
                return None, {"reason": "both-complementary-arcs-forced-short", "witness": witnesses[-1]}
            if forward:
                edge(i, j, caps[h])
            if backward:
                edge(j, i, caps[h] - SCALE)
    result = [[None] * b for _ in range(b)]
    for i in range(b):
        result[i][i] = 0
    for (i, j), value in edges.items():
        result[i][j] = value
    for w in range(b):
        for i in range(b):
            for j in range(b):
                if result[i][w] is not None and result[w][j] is not None:
                    proposed = result[i][w] + result[w][j]
                    if result[i][j] is None or result[i][j] > proposed:
                        result[i][j] = proposed
    if any(result[i][i] < 0 for i in range(b)):
        return None, {"reason": "negative-difference-cycle"}
    if any(value is None for row in result for value in row):
        raise ValueError("partial anchor difference closure is disconnected")
    return result, {"center_distances_rebuilt_by_BFS": True,
                    "independent_integer_Floyd_closure": True,
                    "direct_difference_edges": [[i, j, value] for (i, j), value in sorted(edges.items())],
                    "forced_arc_path_witnesses": witnesses}
