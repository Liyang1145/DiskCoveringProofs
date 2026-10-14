#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Rebuild source-derived configuration illustrations with Python's standard library.

This checks visualization inputs and reproducibility, not covering optimality.
The saved root/geometry reports remain mathematical source records; their
acceptance scripts are not executed here. No sampling is used as proof evidence.
"""
from __future__ import annotations

import argparse
import csv
from decimal import Decimal, localcontext
from fractions import Fraction as Q
import hashlib
from html import escape
import io
import json
import math
from pathlib import Path
import sys

BASE = Path(__file__).resolve().parents[1]
INPUTS = BASE / "assets" / "configurations"
COLORS = ("#2563eb", "#b45309", "#15803d", "#9333ea", "#be123c",
          "#0e7490", "#a16207", "#4338ca", "#047857")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_sources():
    manifest = json.loads((INPUTS / "provenance.json").read_text(encoding="utf-8"))
    result, refs = {}, {}
    for row in manifest["sources"]:
        path = INPUTS / row["snapshot"]
        require(path.resolve().is_relative_to(INPUTS.resolve()), "Source path escapes inputs")
        raw = path.read_bytes()
        require(len(raw) == row["snapshot_bytes"], f"Source size mismatch: {path.name}")
        require(hashlib.sha256(raw).hexdigest() == row["snapshot_sha256"],
                f"Source SHA256 mismatch: {path.name}")
        if row["copy_kind"] == "verbatim":
            require(row["original_sha256"] == row["snapshot_sha256"], "Invalid verbatim hash")
        if path.suffix == ".json":
            result[path.name] = json.loads(raw)
        refs[path.name] = row
    return result, refs


def decimal(q, places=12):
    with localcontext() as ctx:
        ctx.prec = max(100, places + 20)
        q = Q(q)
        return format((Decimal(q.numerator) / Decimal(q.denominator))
                      .quantize(Decimal(1).scaleb(-places)), "f")


def stable_radius(lo, hi):
    require(Q(0) < Q(lo) < Q(hi) < Q(1), "Invalid radius enclosure")
    out = decimal(lo, 20)
    require(out == decimal(hi, 20), "Source enclosure does not justify 20 rounded places")
    return out


def mid(interval):
    return (Q(interval[0]) + Q(interval[1])) / 2


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def neg(x):
    return (-x[1], -x[0])


def scale(x, c):
    return (x[0] * c, x[1] * c) if c >= 0 else (x[1] * c, x[0] * c)


def rotate_scaled(p):
    # Exact 120 degree rotation for the physical point (x, Y / sqrt(3)).
    x, y = p
    return (scale(neg(add(x, y)), Q(1, 2)),
            scale(add(scale(x, Q(3)), neg(y)), Q(1, 2)))


def turn(p, k):
    for _ in range(k):
        p = rotate_scaled(p)
    return p


def coordinates(points, formulas, enclosures=None):
    rows = []
    for i, ((x, y), formula) in enumerate(zip(points, formulas)):
        row = {"id": i, "x_approx": format(x, ".12f"), "y_approx": format(y, ".12f"),
               "exact_definition": formula,
               "approximation_scope": "Drawing coordinates rounded to 12 places; not exact rational centers."}
        if enclosures is not None:
            row["source_coordinate_enclosure"] = enclosures[i]
        rows.append(row)
    return rows


def configuration11(s, refs):
    root = s["n11-root.json"]
    shared_input = BASE / "math_data" / "n11" / "root_input.json"
    if shared_input.exists():
        shared = json.loads(shared_input.read_text(encoding="utf-8"))
        require(shared["center_hex"] == root["certificate"]["center_hex"]
                and shared["radius_hex"] == root["certificate"]["radius_hex"]
                and shared["source"]["sha256"] == refs["n11-root.json"]["original_sha256"],
                "Gallery and n11 checker select different exact root boxes")
    z = list(map(float, root["numeric_root"][:7]))
    a = z[:4] + [math.pi - 2 * sum(z[:4])] + list(reversed(z[:4]))
    r = z[6]
    rho = [math.cos(v) - math.sqrt(r * r - math.sin(v) ** 2) for v in a]
    theta = [0.0] * 9
    for k in range(5, 9):
        theta[k] = theta[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        theta[k] = theta[k + 1] - a[k] - a[k + 1]
    pts = [(rho[k] * math.cos(theta[k]), rho[k] * math.sin(theta[k])) for k in range(9)]
    pts += [(z[4], 0.0), (z[5], 0.0)]
    require(root["certificate"]["pass_inclusion"] and root["certificate"]["contraction_lt1"],
            "n11 source root report not accepted")
    lo, hi = s["n11-radius.json"]["R_exact_rational_enclosure"]
    return {
        "n": 11, "label": "11 disks: symmetric TC/KKT source candidate",
        "radius": {"rounded_20_places": stable_radius(lo, hi), "rational_enclosure": [lo, hi],
                   "exact_definition": "Coordinate 6 of the unique 12-dimensional symmetric TC/KKT root in n11-root.json's dyadic box; the contracted enclosure is n11-radius.json.",
                   "minimal_polynomial": None},
        "root_box": {"center_hex": root["certificate"]["center_hex"],
                     "halfwidth_hex": root["certificate"]["radius_hex"],
                     "dimension": 12, "radius_coordinate": 6},
        "coordinate_definition": "a=(z0,z1,z2,z3,pi-2*(z0+z1+z2+z3),z3,z2,z1,z0); theta4=0, theta[k+1]-theta[k]=a[k]+a[k+1]; rho[k]=cos(a[k])-sqrt(r^2-sin(a[k])^2). See the verbatim geometry source for the cyclic convention.",
        "centers": coordinates(pts, [f"rho[{k}]*(cos(theta[{k}]),sin(theta[{k}]))" for k in range(9)]
                               + ["(z4,0)", "(z5,0)"]),
        "source_faces": [row["face"] for row in s["n11-triangulation.json"]["faces"]],
        "graph_kind": "Source's 11 triangular faces, not a disk-tangency graph. Active equalities require root equations.",
        "symmetry": {"documented_candidate_symmetry": "Reflection across the x axis, by the displayed parametrization", "full_symmetry_group_classification": None},
        "sources": [refs[k] for k in refs if k.startswith("n11")],
    }


def configuration12(s, refs):
    root, geom = s["n12-root.json"], s["n12-geometry.json"]
    require(root["status"] == "certified", "n12 source root report not certified")
    require(geom["root_box"] == root["box"], "n12 geometry uses a different root box")
    require(root["vars"] == ["a", "t", "r", "w"], "Unexpected n12 coordinate convention")
    a, t, r, w = [tuple(map(Q, pair)) for pair in root["box"]]
    b = scale(add(add((Q(1), Q(1)), a), r), Q(1, 2))
    scaled = []
    formulas = []
    for k in range(3):
        scaled += [turn((b, w), k), turn((scale(t, Q(1, 2)), scale(t, Q(3, 2))), k),
                   turn((b, neg(w)), (k + 1) % 3)]
        formulas += [f"rot^{k}(b,w/sqrt(3))", f"rot^{k}(t/2,sqrt(3)*t/2)",
                     f"rot^{(k + 1) % 3}(b,-w/sqrt(3))"]
    scaled += [turn((a, (Q(0), Q(0))), k) for k in range(3)]
    formulas += [f"rot^{k}(a,0)" for k in range(3)]
    serialized = [[[str(v) for v in interval] for interval in p] for p in scaled]
    require(serialized == geom["centers_scaled"], "n12 exact interval extraction disagrees with source")
    pts = [(float(mid(x)), float(mid(y)) / math.sqrt(3)) for x, y in scaled]
    enc = [{"coordinate_system": "x, Y=sqrt(3)*y", "x": row[0], "Y": row[1]}
           for row in serialized]
    lo, hi = root["image"][2]
    return {
        "n": 12, "label": "12 disks: F,G,H,T source candidate",
        "radius": {"rounded_20_places": stable_radius(lo, hi), "rational_enclosure": [lo, hi],
                   "exact_definition": "The r coordinate of the unique common root of the four polynomials F,G,H,T in sources/n12-root.json's rational box.", "minimal_polynomial": None},
        "root_variables": root["vars"], "root_polynomials": root["polynomials"],
        "root_box": root["box"],
        "coordinate_definition": "b=(1+a+r)/2; rot is rotation by 120 degrees. In scaled coordinates (x,Y=sqrt(3)*y), rot(x,Y)=((-x-Y)/2,(3*x-Y)/2). Center IDs retain the source's ordering.",
        "centers": coordinates(pts, formulas, enc),
        "source_faces": [row["face"] for row in geom["faces"]],
        "graph_kind": "Source's 13 triangular faces; no claim that these edges are disk tangencies.",
        "symmetry": {"documented_candidate_symmetry": "D3 (120 degree rotations and a reflection), directly from the coordinate formula", "full_symmetry_group_classification": None},
        "sources": [refs[k] for k in refs if k.startswith("n12")],
    }


def configuration14(s, refs):
    root, geom = s["n14-root.json"], s["n14-geometry.json"]
    require(root["status"] == "certified_local_root", "n14 source root is not certified")
    z, c, r = [float(mid(pair)) for pair in root["Krawczyk_dyadic"]]
    ss = math.sqrt(1-r*r)
    a = (ss+z)/2
    t = r+math.sqrt(r*r-z*z)
    b = r+math.sqrt(r*r-(a-z)**2)
    d = 1-math.sqrt(r*r-c*c)
    values = {"a":a, "b":b, "c":c, "d":d, "s":ss, "z":z, "t":t, "0":0.0}
    def value(name):
        return -values[name[1:]] if name.startswith("-") else values[name]
    pts = [(value(x), value(y)) for x,y in geom["center_order_symbolic"]]
    lo, hi = root["Krawczyk_dyadic"][2]
    return {
        "n":14, "label":"14 disks: F,G,H radical-system source candidate",
        "radius":{"rounded_20_places":stable_radius(lo,hi), "rational_enclosure":[lo,hi],
                  "exact_definition":"r coordinate of the unique F,G,H root in n14-root.json's dyadic box, using positive radical branches. Equations and coordinates are specified in n14-definition.md.", "minimal_polynomial":None},
        "root_variables":["z","c","r"], "root_box":root["box_dyadic"],
        "coordinate_definition":"s=sqrt(1-r^2), a=(s+z)/2, t=r+sqrt(r^2-z^2), b=r+sqrt(r^2-(a-z)^2), d=1-sqrt(r^2-c^2). All square roots are positive. Center order comes from n14-geometry.json.",
        "centers":coordinates(pts,[f"({x},{y})" for x,y in geom["center_order_symbolic"]]),
        "source_faces":[f["ids"] for f in geom["remaining_triples"]],
        "graph_kind":"16 source nearest-site triangles, including two strict slack triangles; not disk tangencies.",
        "symmetry":{"documented_candidate_symmetry":"D2 (reflections across both coordinate axes), directly from the coordinate formula", "full_symmetry_group_classification":None},
        "sources":[refs[k] for k in refs if k.startswith("n14")],
    }


def configuration22(s, refs):
    core, root, report = s["n22-core-system.json"], s["n22-core-root-extract.json"], s["n22-root-verified.json"]
    require(root["system_sha256"] == refs["n22-core-system.json"]["original_sha256"] == report["system_sha256"], "n22 system identity mismatch")
    require(root["original_root_sha256"] == report["root_sha256"] == s["n22-symmetry.json"]["root_sha256"], "n22 root identity mismatch")
    require(report["verified"] and s["n22-upper-verified.json"]["same_core_root_entire_disk_upper"], "n22 reports not accepted")
    qx, rho = int(root["Qx"]), Q(1, 10**80)
    z = [Q(int(v), qx) for v in root["xnum"]]
    require(len(z) == core["G"] + 1, "Incomplete n22 coordinate seed")
    centers, enc, formulas = [], [], []
    for node in core["center_core_nodes"]:
        require(node is not None and node > 0, "Unexpected n22 fixed center")
        x, y = z[2 * node - 2:2 * node]
        centers.append((float(x), float(y)))
        enc.append({"coordinate_system": "Cartesian x,y", "x": [str(x-rho), str(x+rho)], "y": [str(y-rho), str(y+rho)]})
        formulas.append(f"(z[{2*node-2}],z[{2*node-1}]), for the isolated 252-dimensional core root")
    lo, hi = report["r_strict_interval"]
    p = lambda t: 29*t**3 - 55*t**2 + 19*t - 1
    require(p(Q(lo)**2) < 0 < p(Q(hi)**2), "n22 radius report disagrees with the linked cubic")
    require(Q(lo)**2 < z[core["G"]]-rho < z[core["G"]]+rho < Q(hi)**2, "n22 radius interval disagrees with the root seed")
    # The radius-link proof also supplies a small, complete exact construction.
    # Cross-check the formula against the extracted source seed for plotting.
    rr = float(mid((lo,hi)))
    angle = 2*math.pi/7
    cc, ss = math.cos(angle), math.sin(angle)
    aa = 2*rr*math.cos(angle/2)
    xx = (1+4*aa*aa-rr*rr)/(4*aa)
    yy = -(1-cc)*(1-rr*rr)/(4*aa*ss)
    e = (xx,-yy)
    orbit = [(e[0]*math.cos(k*angle)-e[1]*math.sin(k*angle),
              e[0]*math.sin(k*angle)+e[1]*math.cos(k*angle)) for k in range(7)]
    closed_centers, closed_formulas = [], []
    for k in range(7):
        closed_centers += [(aa*(orbit[(k-1)%7][0]+orbit[k][0]),aa*(orbit[(k-1)%7][1]+orbit[k][1])),
                           (2*aa*orbit[k][0],2*aa*orbit[k][1])]
        closed_formulas += [f"a*(R^{(k-1)%7}*e+R^{k}*e)",f"2*a*R^{k}*e"]
    closed_centers += [(aa*e[0],aa*e[1]),(0,0)]
    closed_formulas += ["a*e","(0,0)"]
    for k in (4,5,6,1,2,3):
        closed_centers.append((aa*orbit[k][0],aa*orbit[k][1]))
        closed_formulas.append(f"a*R^{k}*e")
    require(max(abs(v-w) for p,q in zip(centers,closed_centers) for v,w in zip(p,q)) < 1e-12,
            "n22 closed-form center ordering disagrees with source extraction")
    return {
        "n": 22, "label": "22 disks: D7 core-root source candidate",
        "radius": {"rounded_20_places": stable_radius(lo, hi), "rational_enclosure": [lo, hi],
                   "exact_definition": "r=sqrt(t), where t is the unique root of 29*t^3-55*t^2+19*t-1 in (641/10000,321/5000). The source radius-link record identifies this with the full core root.",
                   "polynomial_variable": "t=r^2", "polynomial_coefficients_descending": [29,-55,19,-1],
                   "isolating_interval_for_t": ["641/10000", "321/5000"],
                   "minimal_polynomial": "29*t^3-55*t^2+19*t-1 (for squared radius t)"},
        "coordinate_definition": "theta=2*pi/7, c=cos(theta), s=sin(theta), a=2*r*cos(theta/2), X=(1+4*a^2-r^2)/(4*a), Y=-(1-c)*(1-r^2)/(4*a*s), e=(X,-Y); R rotates by theta. Center formulas below use the exact linked radius r. The source core-root extract independently supplies drawing-coordinate enclosures: node j is (z[2j-2],z[2j-1]), z in xnum/Qx +/- 10^-80. Boundary anchors and auxiliary face witnesses are not centers.",
        "centers": coordinates(centers, closed_formulas, enc),
        "source_faces": core["all_faces"],
        "graph_kind": "28 center triangles from the core-system; source active-face graph, not a disk-tangency graph.",
        "symmetry": {"documented_candidate_symmetry": "D7, identified by source root-box transports in n22-radius-link.md and n22-symmetry.json", "full_symmetry_group_classification": None},
        "sources": [refs[k] for k in refs if k.startswith("n22")],
    }


def configuration25(s, refs):
    geom, report = s["n25-geometry.json"], s["n25-upper-verified.json"]
    require(report["verified"] and report["geometry_sha256"] == refs["n25-geometry.json"]["original_sha256"], "n25 geometry identity mismatch")
    require(geom["a_squared"] == ["2/3","-1/3"] and geom["r_squared"] == ["1","-2/3"], "Unexpected n25 field convention")
    with localcontext() as ctx:
        ctx.prec = 100
        sqrt2 = Decimal(2).sqrt()
        a = ((2-sqrt2)/3).sqrt()
        def field(pair):
            return Decimal(Q(pair[0]).numerator)/Decimal(Q(pair[0]).denominator) + sqrt2*Decimal(Q(pair[1]).numerator)/Decimal(Q(pair[1]).denominator)
        pts = [(float(a*field(x)),float(a*field(y))) for x,y in geom["centers"]]
    lo,hi = report["r_strict_interval"]
    formulas = [f"a*({x[0]}+({x[1]})*sqrt(2), {y[0]}+({y[1]})*sqrt(2))" for x,y in geom["centers"]]
    return {
        "n":25, "label":"25 disks: exact quadratic-field source candidate",
        "radius":{"rounded_20_places":stable_radius(lo,hi), "rational_enclosure":[lo,hi],
                  "exact_definition":"r=1/(sqrt(6)+sqrt(3)); r^2=1-2*sqrt(2)/3. Exact construction uses Q(sqrt(2)) times a=sqrt((2-sqrt(2))/3).",
                  "minimal_polynomial":"9*t^2-18*t+1 (for squared radius t)",
                  "polynomial_variable":"t=r^2", "polynomial_coefficients_descending":[9,-18,1],
                  "isolating_interval_for_t":["57/1000","58/1000"]},
        "coordinate_definition":"a=sqrt((2-sqrt(2))/3); each stored coefficient pair [u,v] represents u+v*sqrt(2). Physical centers are a times these coefficients. No fitted floating point centers are used.",
        "coordinate_coefficients_Q_sqrt2":geom["centers"],
        "centers":coordinates(pts,formulas), "source_faces":geom["faces"],
        "graph_kind":"32 source active center triangles; not disk tangencies.",
        "symmetry":{"documented_candidate_symmetry":None,"full_symmetry_group_classification":None},
        "sources":[refs[k] for k in refs if k.startswith("n25")],
    }


def radius_index(configs, s, refs):
    rows = [{"n":c["n"], **c["radius"], "documented_candidate_symmetry":c["symmetry"]["documented_candidate_symmetry"],
             "coordinate_table":"coordinates.csv", "figure":f"n{c['n']}.svg", "sources":c["sources"]} for c in configs]
    for n in (21,23,24):
        key = f"n{n}-root-verified.json"
        report = s[key]
        require(report["verified"],f"n{n} source root report not verified")
        lo,hi = report["r_strict_interval"]
        rows.append({"n":n,"rounded_20_places":stable_radius(lo,hi),"rational_enclosure":[lo,hi],
                     "exact_definition":f"sqrt of the radius-squared coordinate of the isolated core root identified by root SHA256 {report['root_sha256']} and system SHA256 {report['system_sha256']}. The supplied snapshot is the source verifier's report, not the root itself.",
                     "minimal_polynomial":None, "documented_candidate_symmetry":None,
                     "coordinate_table":None,"figure":None,"sources":[refs[key]]})
    return {"schema":"disk-covering-radius-navigation-v1", "generated_output_license":"MIT; raw source reports retain their original scope", "scope":"Source candidate radii. Rounded 20-place displays are justified by identical rounding of both saved enclosure endpoints; this index does not reprove global lower bounds.", "entries":sorted(rows,key=lambda x:x["n"])}


def arc_segments(x, y, r):
    distance = math.hypot(x, y)
    if distance == 0:
        return [(0, 2*math.pi)] if r >= 1 else []
    threshold = (1 + distance*distance - r*r) / (2*distance)
    if threshold >= 1:
        return []
    if threshold <= -1:
        return [(0, 2*math.pi)]
    half, phi = math.acos(threshold), math.atan2(y, x) % (2*math.pi)
    lo, hi = phi-half, phi+half
    if lo < 0:
        return [(0, hi), (lo+2*math.pi, 2*math.pi)]
    if hi > 2*math.pi:
        return [(lo, 2*math.pi), (0, hi-2*math.pi)]
    return [(lo, hi)]


def svg(config):
    pts = [(float(c["x_approx"]), float(c["y_approx"])) for c in config["centers"]]
    r = float(config["radius"]["rounded_20_places"])
    n, size, radius_px = config["n"], 360, 145
    out = ['<!-- SPDX-License-Identifier: MIT; first-party generated illustration. Raw source certificates retain their original scope. -->',
           f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1080 450" role="img" aria-labelledby="title desc">',
           f'<title id="title">Source configuration for n={n}</title>',
           '<desc id="desc">Three views: equal-radius disks clipped to the unit disk, the source center triangulation, and each center&#39;s boundary coverage arc. Approximate illustration; not a proof or a uniqueness claim.</desc>',
           '<rect width="1080" height="450" fill="#f8fafc"/>',
           f'<text x="24" y="30" font-family="sans-serif" font-size="20" fill="#0f172a">n = {n} | r = {escape(config["radius"]["rounded_20_places"])}</text>']
    headings = ["Equal-radius covering disks", "Source center triangulation", "Boundary coverage arcs"]
    for panel, heading in enumerate(headings):
        cx, cy = panel*size + size/2, 222
        out += [f'<text x="{cx}" y="61" text-anchor="middle" font-family="sans-serif" font-size="15" fill="#334155">{heading}</text>',
                f'<defs><clipPath id="clip{panel}"><circle cx="{cx}" cy="{cy}" r="{radius_px}"/></clipPath></defs>',
                f'<circle cx="{cx}" cy="{cy}" r="{radius_px}" fill="white" stroke="#475569" stroke-width="1.3"/>']
        if panel == 0:
            out.append(f'<g clip-path="url(#clip{panel})">')
            for i, (x, y) in enumerate(pts):
                out.append(f'<circle cx="{cx+x*radius_px:.6f}" cy="{cy-y*radius_px:.6f}" r="{r*radius_px:.6f}" fill="{COLORS[i%len(COLORS)]}" fill-opacity="0.10" stroke="{COLORS[i%len(COLORS)]}" stroke-opacity="0.65" stroke-width="1"/>')
            out.append('</g>')
        if panel == 1:
            edges = sorted({tuple(sorted((f[i], f[(i+1)%3]))) for f in config["source_faces"] for i in range(3)})
            for a, b in edges:
                x, y = pts[a]; u, v = pts[b]
                out.append(f'<line x1="{cx+x*radius_px:.6f}" y1="{cy-y*radius_px:.6f}" x2="{cx+u*radius_px:.6f}" y2="{cy-v*radius_px:.6f}" stroke="#64748b" stroke-width="1.4"/>')
        if panel == 2:
            for i, (x, y) in enumerate(pts):
                band = radius_px + 2.3*(i % 4)
                for lo, hi in arc_segments(x,y,r):
                    xx, yy = cx+band*math.cos(lo), cy-band*math.sin(lo)
                    uu, vv = cx+band*math.cos(hi), cy-band*math.sin(hi)
                    out.append(f'<path d="M {xx:.6f},{yy:.6f} A {band:.6f},{band:.6f} 0 {int(hi-lo>math.pi)} 0 {uu:.6f},{vv:.6f}" fill="none" stroke="{COLORS[i%len(COLORS)]}" stroke-width="3.2"/>')
        for i, (x, y) in enumerate(pts):
            px, py = cx+x*radius_px, cy-y*radius_px
            out += [f'<circle cx="{px:.6f}" cy="{py:.6f}" r="2.8" fill="{COLORS[i%len(COLORS)]}"/>',
                    f'<text x="{px+5:.6f}" y="{py-5:.6f}" font-family="sans-serif" font-size="10" fill="#0f172a">{i}</text>']
    out += ['<text x="24" y="408" font-family="sans-serif" font-size="12" fill="#475569">Source-derived candidate. Center IDs match configurations.json. Edges connect triangle vertices; they do not denote disk tangency.</text>',
            '<text x="24" y="430" font-family="sans-serif" font-size="12" fill="#475569">Arcs use double-precision circle intersections and slightly offset tracks for readability. Illustration does not certify arc closure or global optimality.</text>',
            '</svg>']
    return "\n".join(out) + "\n"


def artifacts():
    s, refs = load_sources()
    configs = [configuration11(s,refs), configuration12(s,refs), configuration14(s,refs),
               configuration22(s,refs), configuration25(s,refs)]
    for conf in configs:
        n = conf["n"]
        require(len(conf["centers"]) == n, "Wrong center count")
        for f in conf["source_faces"]:
            require(len(f) == 3 and len(set(f)) == 3 and all(0 <= k < n for k in f), "Invalid source face")
        conf["proof_scope"] = "Source candidate/attainment illustration. This generator does not verify root isolation, every terminal box, global optimality, or uniqueness of optimal covers."
    catalogue = {"schema": "disk-covering-configuration-gallery-v1", "generated_output_license":"MIT; raw snapshots under sources/ retain their original scope", "normalization": "closed unit disk, Euclidean equal-radius covering disks", "configurations": configs}
    out = {"configurations.json": json.dumps(catalogue, indent=2, ensure_ascii=False) + "\n"}
    out["radius-index.json"] = json.dumps(radius_index(configs,s,refs),indent=2,ensure_ascii=False) + "\n"
    stream = io.StringIO(newline="")
    writer = csv.writer(stream, lineterminator="\n")
    writer.writerow(["n", "center_id", "x_approx", "y_approx", "exact_definition"])
    for conf in configs:
        for row in conf["centers"]:
            writer.writerow([conf["n"], row["id"], row["x_approx"], row["y_approx"], row["exact_definition"]])
        out[f"n{conf['n']}.svg"] = svg(conf)
    out["coordinates.csv"] = stream.getvalue()
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Verify input SHA256 and compare regenerated figures/data with committed bytes")
    parser.add_argument("--output-dir", type=Path, default=INPUTS, help="Directory for rebuilt outputs (source paths stay relative to this repository)")
    args = parser.parse_args()
    generated = artifacts()
    if args.check:
        for name, content in generated.items():
            path = args.output_dir / name
            require(path.is_file() and path.read_bytes() == content.encode("utf-8"), f"Gallery differs: {path}")
        print("GALLERY PASS: 22 source snapshots, 84 centers, 5 configurations, 8 radius entries; input hashes and reproducible output agree. This is not a mathematical proof acceptance run.")
    else:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        for name, content in generated.items():
            (args.output_dir / name).write_bytes(content.encode("utf-8"))
        print(f"Generated {len(generated)} artifacts in {args.output_dir}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, OSError) as exc:
        print(f"GALLERY FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
