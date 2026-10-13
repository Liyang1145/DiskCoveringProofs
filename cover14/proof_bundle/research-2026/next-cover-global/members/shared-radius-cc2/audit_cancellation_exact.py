"""
Settle the cancellation/absolute-value question on an exact configuration.

beta = (pi/2, pi/2, pi/2), R = U = 1:
  u1,u2,u3 = e^{i pi k} (k=0,1,2)  -- wait, sum beta < 2pi requires the u's to
  be pairwise separated by beta_i; with three equal betas = pi/2 the pairwise
  separations cannot all be pi/2 on a single circle (sum = 3pi/2 but the
  separations of 3 points at a common center are beta_12+beta_23+beta_31 = 2pi
  only if the center is inside the triangle).  In the local relaxation the three
  facet triangles are INDEPENDENT (each with its own center A_k), so the model
  below uses independent A_k: this is exactly the local relaxation.
Each facet k: chord-endpoints u_i,u_j with |u_i|=|u_j|=R=1, angle at O =
beta_k = pi/2, and A_k the center of the circle through O,u_i,u_j with
|A_k - u_i| = |A_k - u_j| = T_k (T_k <= U = 1).
Compute: six triangle areas [O, u_i, A_k], [O, A_k, u_j] (signed), their sum,
their SUM OF ABSOLUTE VALUES, and the shoelace area of the walk
u1,A1,u2,A2,u3,A3.  The cap claim is about the sum of the (nonnegative) facet
areas; check both interpretations.
"""
import json
import numpy as np

PI = np.pi
out = {}


def facet(u_i, u_j, T):
    """center of circle through 0,u_i,u_j with radius T (|A-u_i|=T)."""
    M = 0.5 * (u_i + u_j)
    d = np.linalg.norm(M)
    if T < d - 1e-15:
        return None
    dv = u_j - u_i
    perp = np.array([-dv[1], dv[0]])
    perp = perp / np.linalg.norm(perp)
    return M + np.sqrt(max(T ** 2 - d ** 2, 0.0)) * perp


def areas_of(u_i, u_j, A):
    O = np.zeros(2)
    t1 = 0.5 * float(np.cross(u_i - O, A - O))
    t2 = 0.5 * float(np.cross(A - O, u_j - O))
    return t1, t2


cases = {}
# Case A: beta = pi/2 for all three facets, independent chords but the SAME
# magnitude R=1;  take u_i on the unit circle at angles 0, pi/2, pi (spacing
# pi/2), and build A_1 for chord (u1,u2), A_2 for (u2,u3), A_3 for (u3,u1)
# with T chosen as the true circumradius of each triangle.
R = 1.0
ang = np.array([0.0, PI / 2, PI])
u = np.stack([R * np.cos(ang), R * np.sin(ang)])
info = {}
for k, (i, j) in enumerate([(0, 1), (1, 2), (2, 0)]):
    chord = np.linalg.norm(u[:, j] - u[:, i])
    beta_k = np.arccos(np.clip(np.dot(u[:, i], u[:, j]) / R ** 2, -1, 1))
    Tk = chord / (2 * np.sin(beta_k))
    A = facet(u[:, i], u[:, j], Tk)
    t1, t2 = areas_of(u[:, i], u[:, j], A)
    info[f'facet{k}'] = dict(i=i, j=j, beta=float(beta_k), chord=float(chord),
                             T=float(Tk), T_le_U=bool(Tk <= 1 + 1e-12),
                             A=A.tolist(), t1=t1, t2=t2,
                             facet_area_formula=float(Tk * np.sin(beta_k)))
    cases.setdefault('A', []).append((u[:, i].copy(), u[:, j].copy(), A))
tot_signed = sum(v['t1'] + v['t2'] for v in info.values())
tot_abs = sum(abs(v['t1']) + abs(v['t2']) for v in info.values())
walk_pts = []
for k, (i, j) in enumerate([(0, 1), (1, 2), (2, 0)]):
    walk_pts.append(u[:, i])
    walk_pts.append(np.array(info[f'facet{k}']['A']))
walk = np.array(walk_pts).T
x, y = walk[0], walk[1]
sa = 0.5 * float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y))
sl = [float(np.linalg.norm(walk[:, (k + 1) % 6] - walk[:, k])) for k in range(6)]
out['case_A'] = dict(info=info, sum_signed=tot_signed, sum_abs=tot_abs,
                     shoelace=sa, side_lengths=sl, side_max=max(sl),
                     bound_3sqrt3_2=3 * np.sqrt(3) / 2,
                     sum_facet_formula=sum(v['facet_area_formula'] for v in info.values()))

# Case B: the standard equilateral-face configuration (beta=pi/3, all T=1)
ang3 = np.array([0.0, 2 * PI / 3, 4 * PI / 3])
u3 = np.stack([np.cos(ang3), np.sin(ang3)])
infoB = {}
for k, (i, j) in enumerate([(0, 1), (1, 2), (2, 0)]):
    chord = np.linalg.norm(u3[:, j] - u3[:, i])
    beta_k = np.arccos(np.clip(np.dot(u3[:, i], u3[:, j]), -1, 1))
    Tk = chord / (2 * np.sin(beta_k))
    A = facet(u3[:, i], u3[:, j], Tk)
    t1, t2 = areas_of(u3[:, i], u3[:, j], A)
    infoB[f'facet{k}'] = dict(beta=float(beta_k), T=float(Tk), t1=t1, t2=t2,
                              A=A.tolist())
    walk_pts.append(None)
walkB = []
for k, (i, j) in enumerate([(0, 1), (1, 2), (2, 0)]):
    walkB.append(u3[:, i]); walkB.append(np.array(infoB[f'facet{k}']['A']))
walkB = np.array(walkB).T
xB, yB = walkB[0], walkB[1]
saB = 0.5 * float(np.sum(xB * np.roll(yB, -1) - np.roll(xB, -1) * yB))
slB = [float(np.linalg.norm(walkB[:, (k + 1) % 6] - walkB[:, k])) for k in range(6)]
out['case_B_equilateral'] = dict(info=infoB,
                                 sum_signed=sum(v['t1'] + v['t2'] for v in infoB.values()),
                                 sum_abs=sum(abs(v['t1']) + abs(v['t2']) for v in infoB.values()),
                                 shoelace=saB, side_lengths=slB, side_max=max(slB),
                                 bound_3sqrt3_2=3 * np.sqrt(3) / 2)
print(json.dumps(out, indent=1))
with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\cancellation_exact.json", 'w') as f:
    json.dump(out, f, indent=1)
