"""Exact same-root geometry transport and continuous disk cover.

Standard library only. All acceptance uses integers/Fraction; no floating
geometry, numerical triangulation, or numerical polynomial factorization.
See PROOF.md in the published bundle for the winding/coverage lemmas.
"""

import argparse
from collections import defaultdict, deque
from copy import deepcopy
from fractions import Fraction as F
from functools import reduce
from math import gcd
from pathlib import Path
import json

import verify_contact_root as root


D = 14
ONE = {(0,) * D: F(1)}


def clean(p):
    return {e: c for e, c in p.items() if c}


def pa(a, b):
    result = a.copy()
    for e, c in b.items():
        result[e] = result.get(e, F(0)) + c
    return clean(result)


def ps(a, b):
    return pa(a, {e: -c for e, c in b.items()})


def pm(a, b):
    result = {}
    for e, c in a.items():
        for f, d in b.items():
            g = tuple(x + y for x, y in zip(e, f))
            result[g] = result.get(g, F(0)) + c * d
    return clean(result)


def pk(k, a):
    return clean({e: k * c for e, c in a.items()})


def pp(a):
    return pm(a, a)


def variable(j, sign=1):
    e = [0] * D
    e[j] = 1
    return {tuple(e): F(sign)}


def primitive(p):
    if not p:
        raise ValueError("zero polynomial")
    lcm = 1
    for c in p.values():
        lcm = lcm * c.denominator // gcd(lcm, c.denominator)
    integers = {e: int(c * lcm) for e, c in p.items()}
    divisor = reduce(gcd, (abs(c) for c in integers.values()))
    sign = 1 if integers[max(integers)] > 0 else -1
    return {e: F(sign * c // divisor) for e, c in integers.items()}


def read_poly(encoded, dimension):
    decoded = root.decode(encoded, dimension)
    if dimension > D and any(any(e[D:]) for c, e in decoded):
        raise ValueError("contact equation depends on multiplier")
    return clean({e[:D]: c for c, e in decoded})


def divides(divisor, dividend):
    """Exact lexicographic multivariate single-divisor division."""
    if not divisor:
        raise ValueError("zero divisor")
    remainder = dividend.copy()
    leading = max(divisor)
    count = 0
    while remainder:
        e = max(remainder)
        if any(a < b for a, b in zip(e, leading)):
            return False
        shift = tuple(a - b for a, b in zip(e, leading))
        factor = remainder[e] / divisor[leading]
        subtract = {tuple(a + b for a, b in zip(f, shift)): factor * c
                    for f, c in divisor.items()}
        remainder = ps(remainder, subtract)
        count += 1
        if count > 20000:
            raise ValueError("polynomial division budget exceeded")
    return True


def vsub(a, b, subtract):
    return [subtract(x, y) for x, y in zip(a, b)]


def pcross(a, b):
    return ps(pm(a[0], b[1]), pm(a[1], b[0]))


def pnorm(a):
    return pa(pp(a[0]), pp(a[1]))


def face_poly(points, face):
    a, b, c = [points[i] for i in face]
    det = pcross(vsub(b, a, ps), vsub(c, a, ps))
    lengths = [pnorm(vsub(x, y, ps)) for x, y in ((a, b), (b, c), (c, a))]
    return ps(pk(4, pm(variable(13), pp(det))), pm(pm(lengths[0], lengths[1]), lengths[2]))


def boundary_poly(points, i):
    a, b = points[i], points[(i + 1) % 16]
    h, k = [ps(pa(ONE, pnorm(p)), variable(13)) for p in (a, b)]
    nx = ps(pm(h, b[1]), pm(a[1], k))
    ny = ps(pm(a[0], k), pm(h, b[0]))
    return ps(pa(pp(nx), pp(ny)), pk(4, pp(pcross(a, b))))


def ivdiv(a, b):
    if b[0] <= 0 <= b[1]:
        raise ValueError("division determinant can vanish")
    return root.mul(a, (1 / b[1], 1 / b[0]))


def ivcross(a, b):
    return root.sub(root.mul(a[0], b[1]), root.mul(a[1], b[0]))


def ivnorm(a):
    return root.add(root.mul(a[0], a[0]), root.mul(a[1], a[1]))


def ivdist(a, b):
    return ivnorm(vsub(a, b, root.sub))


def nonzero(interval):
    return interval[0] > 0 or interval[1] < 0


def circumcenter(points, face):
    a, b, c = [points[i] for i in face]
    u, v = vsub(b, a, root.sub), vsub(c, a, root.sub)
    det = root.scale(F(2), ivcross(u, v))
    if not nonzero(det):
        raise ValueError("center face determinant not separated from zero")
    uu, vv = ivnorm(u), ivnorm(v)
    x = ivdiv(root.sub(root.mul(uu, v[1]), root.mul(u[1], vv)), det)
    y = ivdiv(root.sub(root.mul(u[0], vv), root.mul(uu, v[0])), det)
    return [root.add(a[0], x), root.add(a[1], y)]


def mesh_check(center_faces):
    if len(center_faces) != 34:
        raise ValueError("wrong center face count")
    faces = [tuple(f) for f in center_faces]
    for i in range(16):
        faces.extend(((26 + (i - 1) % 16, 26 + i, i),
                      (26 + i, (i + 1) % 16, i)))
    if len({tuple(sorted(f)) for f in faces}) != len(faces):
        raise ValueError("duplicate mesh face")
    if any(len(set(f)) != 3 or any(type(v) is not int or not 0 <= v < 42 for v in f)
           for f in faces):
        raise ValueError("invalid mesh face")
    incidence = defaultdict(list)

    def edges(f):
        return [(f[i], f[(i + 1) % 3]) for i in range(3)]

    for j, face in enumerate(faces):
        for a, b in edges(face):
            incidence[tuple(sorted((a, b)))].append((j, a, b))
    boundary = {tuple(sorted((26 + i, 26 + (i + 1) % 16))) for i in range(16)}
    if {e for e, occurrences in incidence.items() if len(occurrences) == 1} != boundary:
        raise ValueError("wrong mesh boundary")
    if any(len(v) != (1 if e in boundary else 2) for e, v in incidence.items()):
        raise ValueError("nonmanifold edge")
    if len(incidence) != 107 or 42 - len(incidence) + len(faces) != 1:
        raise ValueError("wrong Euler data")
    start = faces.index((41, 26, 0))
    orientation = {start: 1}
    queue = deque([start])
    while queue:
        j = queue.popleft()
        for a, b in edges(faces[j]):
            for k, x, y in incidence[tuple(sorted((a, b)))]:
                if k == j:
                    continue
                wanted = -orientation[j] if (x, y) == (a, b) else orientation[j]
                if k in orientation and orientation[k] != wanted:
                    raise ValueError("mesh not coherently orientable")
                if k not in orientation:
                    orientation[k] = wanted
                    queue.append(k)
    if len(orientation) != len(faces):
        raise ValueError("mesh disconnected")
    chain = defaultdict(int)
    for j, face in enumerate(faces):
        for a, b in edges(face):
            chain[a, b] += orientation[j]
            chain[b, a] -= orientation[j]
    expected = defaultdict(int)
    for i in range(16):
        a, b = 26 + i, 26 + (i + 1) % 16
        expected[a, b] += 1
        expected[b, a] -= 1
    if clean(chain) != clean(expected):
        raise ValueError("oriented mesh chain is not the anchor cycle")
    # Each vertex link is a single circle (interior) or interval (boundary).
    for v in range(42):
        link = defaultdict(set)
        for face in faces:
            if v in face:
                a, b = [u for u in face if u != v]
                link[a].add(b)
                link[b].add(a)
        if not link:
            raise ValueError("unused mesh vertex")
        visited = set()
        pending = [next(iter(link))]
        while pending:
            w = pending.pop()
            if w not in visited:
                visited.add(w)
                pending.extend(link[w] - visited)
        degrees = sorted(len(neighbors) for neighbors in link.values())
        target = ([1, 1] + [2] * (len(degrees) - 2)) if v >= 26 else [2] * len(degrees)
        if len(visited) != len(link) or degrees != target:
            raise ValueError("wrong vertex link")
    return {"vertices": 42, "edges": 107, "faces": 66, "boundary_edges": 16,
            "coherent_boundary_chain_verified": True, "vertex_links_verified": True,
            "geometric_face_orientation_required": False}


def geometry_check(system, certificate, slack_override=None):
    if (system["N"], system["B"], system["dimension"], system["radius_squared_index"],
            system["geometry_variable_count"], system["contact_equation_count"]) != (26, 16, 26, 13, 14, 12):
        raise ValueError("wrong geometry dimensions")
    # Fixed candidate chart, checked rather than silently trusted as metadata.
    chart = [(0, None), (2, 3), (4, 5), (6, 7), (None, 1),
             (6, 7), (4, 5), (2, 3), (0, None), (2, 3), (4, 5), (6, 7),
             (None, 1), (6, 7), (4, 5), (2, 3), (12, None), (8, None),
             (10, 11), (None, 9), (10, 11), (8, None), (10, 11), (None, 9),
             (10, 11), (12, None)]
    signs = [(1, 0), (1, 1), (1, 1), (1, 1), (0, 1), (-1, 1), (-1, 1), (-1, 1),
             (-1, 0), (-1, -1), (-1, -1), (-1, -1), (0, -1), (1, -1), (1, -1), (1, -1),
             (1, 0), (1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1),
             (0, -1), (1, -1), (-1, 0)]
    wanted = [[{"variable": j, "sign": k} for j, k in zip(row, sign)]
              for row, sign in zip(chart, signs)]
    if system["center_map"] != wanted:
        raise ValueError("changed candidate coordinate chart")
    polypoints = [[{} if j is None else variable(j, k) for j, k in zip(row, sign)]
                  for row, sign in zip(chart, signs)]
    contacts = [primitive(read_poly(poly, 26)) for poly in system["equations"][:12]]
    if len({tuple(sorted(p.items())) for p in contacts}) != 12:
        raise ValueError("duplicate contact equation")
    faces = system["all_faces"]
    active = {tuple(f) for f in system["active_faces"]}
    slack = {tuple(f["face"]) for f in system["slack_faces"]}
    if len(active) != 30 or len(slack) != 4 or active & slack or active | slack != set(map(tuple, faces)):
        raise ValueError("incomplete center-face classification")
    factors = {tuple(item["face"]): item for item in system["face_factor_checks"]}
    if set(factors) != active or len(system["face_factor_checks"]) != 30:
        raise ValueError("missing or duplicate face factor record")
    transported = set()
    for face in active:
        full = primitive(face_poly(polypoints, face))
        record = factors[face]
        if full != primitive(read_poly(record["full_polynomial"], 14)):
            raise ValueError("face identity not independently reconstructed")
        chosen = primitive(read_poly(record["chosen_polynomial"], 14))
        matches = [j for j, p in enumerate(contacts) if p == chosen]
        if len(matches) != 1 or not divides(chosen, full):
            raise ValueError("face factor does not transport from root equation")
        transported.add(matches[0])
    if {tuple(sorted(e)) for e in system["boundary_edges"]} != {
            tuple(sorted((i, (i + 1) % 16))) for i in range(16)} or len(system["boundary_edges"]) != 16:
        raise ValueError("incomplete boundary center cycle")
    for i in range(16):
        full = primitive(boundary_poly(polypoints, i))
        matches = [j for j, p in enumerate(contacts) if p == full]
        if len(matches) != 1:
            raise ValueError("boundary identity not a root contact equation")
        transported.add(matches[0])
    if transported != set(range(12)):
        raise ValueError("unused or missing contact identity")
    topology = mesh_check(faces)
    rho = F(1, 10**80)
    z = [F(int(value), int(certificate["Qx"])) for value in certificate["xnum"]]
    box = [(value - rho, value + rho) for value in z]
    t = box[13]
    if not 0 < t[0] < t[1] < 1:
        raise ValueError("radius not in (0,1)")
    points = [[root.point(0) if j is None else root.scale(k, box[j])
               for j, k in zip(row, sign)] for row, sign in zip(chart, signs)]
    midpoints = [[root.point(0) if j is None else root.point(k * z[j])
                  for j, k in zip(row, sign)] for row, sign in zip(chart, signs)]
    if any(ivnorm(p)[1] >= 1 for p in points):
        raise ValueError("candidate center not strictly inside unit disk")
    anchors = []
    for i in range(16):
        a, b = points[i], points[(i + 1) % 16]
        h, k = [root.scale(F(1, 2), root.sub(root.add(root.point(1), ivnorm(p)), t))
                for p in (a, b)]
        if min(h[0], k[0]) <= 0:
            raise ValueError("anchor footprint not a short arc")
        det = ivcross(a, b)
        anchors.append([
            ivdiv(root.sub(root.mul(h, b[1]), root.mul(a[1], k)), det),
            ivdiv(root.sub(root.mul(a[0], k), root.mul(h, b[0])), det)])
    anchor_margins = []
    for i, a in enumerate(anchors):
        sign = ((1, 1), (-1, 1), (-1, -1), (1, -1))[i // 4]
        if any(root.scale(k, interval)[0] <= 0 for k, interval in zip(sign, a)):
            raise ValueError("anchor outside required open quadrant")
        b = anchors[(i + 1) % 16]
        cross = ivcross(a, b)
        dot = root.add(root.mul(a[0], b[0]), root.mul(a[1], b[1]))
        if min(cross[0], dot[0]) <= 0:
            raise ValueError("anchors not strictly cyclic with short angular gaps")
        anchor_margins.append(min(cross[0], dot[0]))
    determinants = []
    for face in active:
        a, b, c = [points[i] for i in face]
        det = ivcross(vsub(b, a, root.sub), vsub(c, a, root.sub))
        if not nonzero(det):
            raise ValueError("active center triangle degenerate")
        determinants.append(min(abs(det[0]), abs(det[1])))
        # Recheck that all rational functions used by the circumcenter exist.
        circumcenter(points, face)
    witnesses, slack_margins = [], []
    for face in sorted(slack):
        center = circumcenter(midpoints, face)
        witness = [F(round(interval[0] * 10**12), 10**12) for interval in center]
        if slack_override is not None:
            witness = slack_override
        gaps = [t[0] - ivdist(points[i], list(map(root.point, witness)))[1] for i in face]
        if min(gaps) <= 0:
            raise ValueError("slack witness does not certify all three vertices")
        witnesses.append({"face": list(face), "rational_witness": list(map(str, witness))})
        slack_margins.append(min(gaps))
    edge_margins = []
    for i in range(16):
        gap = 4 * t[0] - ivdist(points[i], points[(i + 1) % 16])[1]
        if gap <= 0:
            raise ValueError("two-disk strip base not covered")
        edge_margins.append(gap)
    # q0 has exact distance R from centers 0 and 1 by the boundary identity.
    other_gaps = [ivdist(anchors[0], points[i])[0] - t[1] for i in range(2, 26)]
    if min(other_gaps) <= 0:
        raise ValueError("q0 does not certify the candidate's exact radius")
    return {
        "independent_contact_identity_transport": {
            "center_faces": 30, "boundary_anchors": 16, "contact_orbits": 12,
            "polynomial_divisions_exact": True},
        "mesh": topology,
        "anchors_cyclic_once_and_unit_norm_from_identities": True,
        "active_face_nondegeneracy_margin_lower": str(min(determinants)),
        "anchor_cross_dot_margin_lower": str(min(anchor_margins)),
        "slack_witnesses": witnesses,
        "slack_squared_radius_margin_lower": str(min(slack_margins)),
        "boundary_base_squared_margin_lower": str(min(edge_margins)),
        "q0_other_centers_squared_distance_margin_lower": str(min(other_gaps)),
        "candidate_exact_covering_radius_proved": True,
        "same_root_entire_disk_cover_proved": True,
        "local_optimality_proved": False,
        "global_optimality_proved": False,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    system_path = args.input / "SYSTEM.json"
    certificate_path = args.input / "ROOT-CERTIFICATE.json"
    system = json.loads(system_path.read_text(encoding="utf-8"))
    certificate = json.loads(certificate_path.read_text(encoding="utf-8"))
    if certificate["system_sha256"] != root.sha(system_path):
        raise ValueError("system/root byte binding failed")
    isolated = root.verify(system, certificate, F(1, 10**80))
    print("Exact root contraction replay passed.", flush=True)
    geometry = geometry_check(system, certificate)
    print("Exact identity, mesh, interval geometry and full-cover checks passed.", flush=True)
    rejected = []

    def reject(label, s, override=None):
        try:
            geometry_check(s, certificate, override)
        except (ValueError, KeyError, TypeError):
            rejected.append(label)
        else:
            raise AssertionError("bad geometry accepted: " + label)

    bad = deepcopy(system)
    bad["all_faces"].pop()
    reject("omitted-center-face", bad)
    bad = deepcopy(system)
    bad["all_faces"][-1] = bad["all_faces"][0]
    reject("duplicated-center-face", bad)
    bad = deepcopy(system)
    bad["center_map"][0][0]["sign"] = -1
    reject("changed-coordinate-chart", bad)
    bad = deepcopy(system)
    bad["face_factor_checks"][0]["chosen_polynomial"][0]["coefficient"] = "100"
    reject("changed-contact-factor", bad)
    bad = deepcopy(system)
    bad["equations"][8] = [{"powers": [0] * 26, "coefficient": "1"}]
    reject("changed-boundary-contact", bad)
    bad = deepcopy(system)
    bad["boundary_edges"].pop()
    reject("missing-boundary-edge", bad)
    reject("invalid-slack-witness", system, [F(0), F(0)])
    args.output.mkdir(parents=True)
    files = [
        (system_path, args.output / "SYSTEM.json"),
        (certificate_path, args.output / "ROOT-CERTIFICATE.json"),
        (Path(root.__file__), args.output / "verify_contact_root.py"),
        (Path(__file__), args.output / "verify_same_root_cover.py"),
        (Path(__file__).with_name("n26-same-root-cover-proof.md"), args.output / "PROOF.md"),
    ]
    for source, target in files:
        # Replays may use the published verifier; source and target still differ.
        target.write_bytes(source.read_bytes())
    report = {
        "schema": "N26-same-isolated-root-full-disk-cover-v1", "verified": True,
        "root": isolated, "geometry": geometry,
        "negative_controls_rejected": rejected,
        "proof_scope": "Exact covering radius of this specified 26-center candidate only",
        "local_optimality_proved": False, "global_optimality_proved": False,
        "files": {target.name: root.sha(target) for source, target in files},
        "source_files": {str(source): root.sha(source) for source, target in files},
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"same_root_entire_disk_cover_proved": True,
                      "candidate_exact_covering_radius_proved": True,
                      "r_strict_interval": isolated["r_strict_interval"],
                      "negative_controls": len(rejected), "global_optimality_proved": False}), flush=True)


if __name__ == "__main__":
    main()
