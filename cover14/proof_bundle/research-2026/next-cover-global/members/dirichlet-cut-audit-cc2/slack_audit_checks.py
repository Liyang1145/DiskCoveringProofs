"""member-side data checks for the DUAL-SLACK-LOCALIZATION audit (read-only; no lead code imported)."""
import json, os
from fractions import Fraction as F

P = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lead")
P = os.path.abspath(P)
root = json.loads(open(os.path.join(P, "root-integer-certificate.json")).read())
base = json.loads(open(os.path.join(P, "fixed-anchor-flow-certificate.json")).read())["runs"][0]
flow = json.loads(open(os.path.join(P, "dual-slack-symmetric-flow.json")).read())
cert = json.loads(open(os.path.join(P, "dual-slack-localization-certificate.json")).read())

D = base["incidence_matrix"]
faces = base["faces"]
owners = base.get("owners")
zz = [[F(x) for x in v] for v in flow["flow_vectors"]]
nv = len(D[0])
nf = len(faces)
print("edges D:", len(D), " nodes nv:", nv, " faces nf:", nf, " owners:", None if owners is None else len(owners))
print("len(flow_vectors):", len(zz), " 3*nf+20 =", 3 * nf + 20, " nv == 14+nf:", nv == 14 + nf)
print("base keys:", sorted(base.keys()))
print("flow keys:", sorted(flow.keys()))
print("root box_dyadic:", root.get("box_dyadic"))

# edge type classification from the incidence rows
types = {"site-witness": 0, "witness-site": 0, "site-site": 0, "witness-witness": 0,
         "anchor(head missing -1)": 0, "two +1": 0, "other": 0}
anchor_edges = []
for e, row in enumerate(D):
    pos = [j for j, x in enumerate(row) if x == 1]
    neg = [j for j, x in enumerate(row) if x == -1]
    if len(pos) == 1 and not neg:
        types["anchor(head missing -1)"] += 1
        anchor_edges.append((e, pos[0]))
    elif len(pos) == 1 and len(neg) == 1:
        a, b = pos[0], neg[0]
        sa, sb = a < 14, b < 14
        key = "site-site" if (sa and sb) else "witness-witness" if (not sa and not sb) else ("site-witness" if sa else "witness-site")
        types[key] += 1
    else:
        types["other"] += 1
print("edge types:", types)
print("anchor edge indices:", [e for e, _ in anchor_edges][:6], "... count", len(anchor_edges),
      " min =", min(e for e, _ in anchor_edges))

# balance in exact arithmetic at every free node
bal = [sum(D[e][j] * zz[e][k] for e in range(len(zz))) for j in range(nv) for k in range(2)]
print("balance all zero:", all(x == 0 for x in bal), " nonzero count:", sum(1 for x in bal if x != 0))

# weights / support
lam = [(zz[e][0] ** 2 + zz[e][1] ** 2) for e in range(len(zz))]
pos = [e for e in range(len(zz)) if lam[e] > 0]
print("positive-weight edges:", len(pos), "of", len(zz), " sites 4,5,8,9 touched:",
      [len([e for e in pos if D[e][j] != 0]) for j in (4, 5, 8, 9)])

# anchor pairing: anchor index by (e - 3nf)//2 and direction consistency with the reference geometry
C = None
zb, cb, rb = [F(str(a)) for a, b in [(x[0], x[1]) for x in root["box_dyadic"]]] if False else (None, None, None)
print("certified intervals:", cert.get("intervals"))
print("radius_lower:", cert.get("radius_lower"), " path_resistance_upper:", cert.get("path_resistance_upper"))
print("status:", cert.get("status"), " ga Error display:", cert.get("gauged_error_display"))

