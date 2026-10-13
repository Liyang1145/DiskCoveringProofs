"""N26-specific exact rod-force lower certificates, including partial graphs.

Standard library only. Derived mathematically from the archived cycle-flow
method; all dimensions, thresholds and angular caps are reconstructed for N26.
"""

from collections import deque
from fractions import Fraction as F
from math import isqrt

from verify_degree_area import U, load_trig


N = 26
D = 10**7
CAPS = (754112, 1555305, 2486507, 3880649)


def spec_gate(spec):
    b, next_vertex, faces = spec["B"], spec["next"], spec["faces"]
    if (spec["N"] != N or b not in (14, 15, 16, 17)
            or type(next_vertex) is not int or not b <= next_vertex <= N
            or len(faces) > 50 - b or len(set(faces)) != len(faces)):
        raise ValueError("invalid N26 partial rod specification")
    used = (1 << b) - 1
    adjacency = [(1 << ((i - 1) % b)) | (1 << ((i + 1) % b)) if i < b else 0
                 for i in range(next_vertex)]
    for face in faces:
        if type(face) is not int or not 0 < face < 1 << next_vertex or face.bit_count() != 3:
            raise ValueError("invalid center-face mask")
        used |= face
        for i in range(next_vertex):
            if face >> i & 1:
                adjacency[i] |= face ^ (1 << i)
    if used != (1 << next_vertex) - 1:
        raise ValueError("unused introduced center")
    return b, next_vertex, faces, adjacency


def rod_graph(spec):
    b, next_vertex, faces, adjacency = spec_gate(spec)
    edges = [(i, b + i) for i in range(b)]
    edges += [(i, b + (i + 1) % b) for i in range(b)]
    for k, face in enumerate(faces):
        edges += [(b + next_vertex + k, b + i) for i in range(next_vertex) if face >> i & 1]
    return b + next_vertex + len(faces), edges


def angular_domain(spec):
    b, next_vertex, faces, adjacency = spec_gate(spec)
    mat = [[10**9] * b for _ in range(b)]
    for i in range(b):
        mat[i][i] = 0
        j = (i + 1) % b
        mat[i][j] = CAPS[0] - (D if j == 0 else 0)
        mat[j][i] = D if j == 0 else 0
    for i in range(b):
        distances = [next_vertex + 1] * next_vertex
        pending = deque((i, (i + 1) % b))
        for v in pending:
            distances[v] = 0
        while pending:
            v = pending.popleft()
            if distances[v] == 3:
                continue
            for w in range(next_vertex):
                if adjacency[v] >> w & 1 and distances[w] > distances[v] + 1:
                    distances[w] = distances[v] + 1
                    pending.append(w)
        for j in range(i + 1, b):
            h = min(distances[j], distances[(j + 1) % b])
            if h > 3:
                continue
            cap = CAPS[h]
            k = j - i
            if min(k, b - k) * CAPS[0] <= cap:
                continue
            forward = k * CAPS[0] < D - cap
            backward = (b - k) * CAPS[0] < D - cap
            if forward and backward:
                raise ValueError("contradictory necessary angle directions")
            if forward:
                mat[i][j] = min(mat[i][j], cap)
            elif backward:
                mat[j][i] = min(mat[j][i], cap - D)
    for k in range(b):
        for i in range(b):
            for j in range(b):
                mat[i][j] = min(mat[i][j], mat[i][k] + mat[k][j])
    if any(mat[i][i] < 0 for i in range(b)):
        raise ValueError("negative necessary angle cycle")
    return mat


def rootbox(mat):
    return ([F(-mat[i][0], D) for i in range(1, len(mat))],
            [F(mat[0][i], D) for i in range(1, len(mat))])


def tighten(mat, lower, upper):
    b = len(mat)
    if len(lower) != b - 1 or len(upper) != b - 1:
        raise ValueError("angular box dimensions disagree")
    lo, hi = [F(0), *map(F, lower)], [F(0), *map(F, upper)]
    if any(a > c for a, c in zip(lo, hi)):
        raise ValueError("reversed angular interval")
    new_lo = [max(lo[i] - F(mat[j][i], D) for i in range(b)) for j in range(b)]
    new_hi = [min(hi[i] + F(mat[i][j], D) for i in range(b)) for j in range(b)]
    if any(a > c for a, c in zip(new_lo, new_hi)):
        return None
    if new_lo[0] != 0 or new_hi[0] != 0:
        raise ValueError("rotation-normalized anchor interval changed")
    return new_lo[1:], new_hi[1:]


def spanning_tree(vertices, edges):
    adjacency = [[] for _ in range(vertices)]
    for k, (u, v) in enumerate(edges):
        if not 0 <= u < vertices or not 0 <= v < vertices or u == v:
            raise ValueError("invalid rod edge")
        adjacency[u].append((v, k))
        adjacency[v].append((u, k))
    parent = [None] * vertices
    parent[0] = (-1, -1)
    order, used = [0], set()
    for u in order:
        for v, k in adjacency[u]:
            if parent[v] is None:
                parent[v] = (u, k)
                used.add(k)
                order.append(v)
    if len(order) != vertices:
        raise ValueError("partial rod graph disconnected")
    return parent, order, tuple(k for k in range(len(edges)) if k not in used)


def ceilroot(value):
    q = isqrt(value)
    return q + (q * q < value)


def force_check(spec, lower, upper, cert, arcs=None):
    b = spec["B"]
    vertices, edges = rod_graph(spec)
    arcs = arcs or load_trig()[0]
    q, lam, beta, cycles = cert["q"], cert["l"], cert["b"], cert["f"]
    parent, order, chords = spanning_tree(vertices, edges)
    if (type(q) is not int or not 0 < q <= 10**18
            or len(lam) != b - 1 or len(beta) != 2 * (b - 1)
            or len(cycles) != 2 * len(chords)
            or any(type(k) is not int or k < 0 for k in lam)
            or any(type(k) is not int for k in beta + cycles)):
        raise ValueError("invalid force certificate coefficients")
    if len(lower) != b - 1 or len(upper) != b - 1:
        raise ValueError("wrong angular box dimension")
    aa, bb = [], []
    for lo, hi in zip(lower, upper):
        if not F(lo) <= F(hi) or F(hi) - F(lo) >= F(1, 2):
            raise ValueError("arc halfplane outside certified domain")
        a, c = arcs.arc_halfplane(F(lo), F(hi))
        aa.append(a)
        bb.append(c)
    balance = [[0, 0] for _ in range(vertices)]
    for i in range(b - 1):
        for d in range(2):
            value = lam[i] * aa[i][d] - beta[2 * i + d] * arcs.QA
            balance[i + 1][d] = value
            balance[0][d] -= value
    flow = [[0, 0] for _ in edges]
    for j, k in enumerate(chords):
        u, v = edges[k]
        for d in range(2):
            value = cycles[2 * j + d] * arcs.QA
            flow[k][d] = value
            balance[u][d] -= value
            balance[v][d] += value
    for v in reversed(order[1:]):
        u, k = parent[v]
        sign = 1 if edges[k][0] == v else -1
        for d in range(2):
            flow[k][d] = sign * balance[v][d]
            balance[u][d] += balance[v][d]
            balance[v][d] = 0
    if any(any(row) for row in balance):
        raise ValueError("force reconstruction leaves divergence residual")
    actual = [[0, 0] for _ in range(vertices)]
    for (u, v), row in zip(edges, flow):
        for d in range(2):
            actual[u][d] += row[d]
            actual[v][d] -= row[d]
    for i in range(1, vertices):
        expected = ([lam[i - 1] * aa[i - 1][d] - beta[2 * (i - 1) + d] * arcs.QA
                     for d in range(2)] if i < b else [0, 0])
        if actual[i] != expected:
            raise ValueError("fresh force divergence recomputation failed")
    if actual[0] != [-sum(actual[i][d] for i in range(1, vertices)) for d in range(2)]:
        raise ValueError("root force divergence failed")
    denominator = sum(ceilroot(x * x + y * y) for x, y in flow)
    if denominator <= 0:
        raise ValueError("zero force certificate")
    numerator = 0
    for i in range(b - 1):
        x, y = beta[2 * i:2 * i + 2]
        numerator += lam[i] * (bb[i] - aa[i][0] * (arcs.QB // arcs.QA))
        numerator -= (ceilroot((x * arcs.QA)**2 + (y * arcs.QA)**2) - x * arcs.QA) * (arcs.QB // arcs.QA)
    required_radius_lower = F(numerator * arcs.QA, arcs.QB * denominator)
    return {"required_radius_lower": str(required_radius_lower),
            "strict_margin_above_U": str(required_radius_lower - U),
            "vertices": vertices, "edges": len(edges), "cycle_edges": len(chords)}


def rationalize(spec, lower, upper, lam, support, flow, arcs=None):
    arcs = arcs or load_trig()[0]
    vertices, edges = rod_graph(spec)
    _, _, chords = spanning_tree(vertices, edges)
    last = None
    for q in (10**6, 10**8, 10**10, 10**12, 10**15):
        cert = {"q": q, "l": [max(0, round(float(value) * q)) for value in lam],
                "b": [round(float(value) * q) for row in support for value in row],
                "f": [round(float(flow[k][d]) * q) for k in chords for d in range(2)]}
        try:
            result = force_check(spec, lower, upper, cert, arcs)
        except (ValueError, ArithmeticError):
            continue
        last = result
        if F(result["strict_margin_above_U"]) > 0:
            return cert, result
    return None, last
