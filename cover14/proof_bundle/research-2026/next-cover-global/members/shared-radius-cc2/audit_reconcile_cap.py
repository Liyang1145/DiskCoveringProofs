"""
Reconcile: the envelope/relaxation allows A = sum sin beta (x=1,y=1) whenever
S(1)=sum theta_i(1,1) <= pi and the branch theta_i<pi-beta_i holds.  The hexagon
cap claims sum_i Qi <= 3sqrt3/2 U^2 with hexagon side lengths <= U.  Check, on an
explicit configuration, which hypothesis fails.

Configuration family: face circumcenter O = 0, face triangle u1,u2,u3 with
|u_i| = R = U = 1, facet triangles (O, u_i, u_{i+1}) with |A_i - u_i| =
|A_i - u_{i+1}| = T_i, and the *facet angle* beta_i = angle(u_i O u_{i+1}).
We take beta_i = pi/2 - delta for the symmetric case and compute:
  - the chord length |u_i u_{i+1}|,
  - what T_i must be for the circle through O,u_i,u_{i+1} to exist with that
    chord  (T_i = R/(2 sin beta_i) for the circle through O and the chord
    subtending beta_i),
  - the hexagon walk and its side lengths, and the shoelace area,
  - the facet area sum with the exact chord-identity construction.
"""
import json
import numpy as np

PI = np.pi
out = {}

for delta in [0.0, 1e-3, 0.05, 0.2, 0.5]:
    beta_sym = PI / 2 - delta
    R = 1.0
    U = 1.0
    # facet triangle area (O,u_i,u_{i+1}) = 0.5 R^2 sin(beta_i)
    facet_area = 0.5 * R * R * np.sin(beta_sym)
    # circumradius of triangle (O,u_i,u_j) with |Ou_i|=|Ou_j|=R and angle beta:
    #   side u_i u_j = 2R sin(beta/2);  T = (u_iu_j)/(2 sin beta)
    chord = 2 * R * np.sin(beta_sym / 2)
    T = chord / (2 * np.sin(beta_sym))
    out[f'delta={delta}'] = dict(beta=beta_sym, facet_area=facet_area,
                                 sum_3_facets=3 * facet_area,
                                 chord=chord, T_facet_circumradius=T,
                                 T_over_U=T / U,
                                 feasible_T_le_U=bool(T <= U + 1e-12),
                                 sum_sin_3beta=3 * np.sin(beta_sym),
                                 x0_if_Bsum_gt_pi=None)

# For beta = pi/2 exactly: T = chord/(2 sin beta) = (2R sin(pi/4))/2 = R/sqrt2
b = PI / 2
R = 1.0
chord = 2 * R * np.sin(b / 2)
T = chord / (2 * np.sin(b))
out['exact_pi2'] = dict(chord=chord, T=T, T_le_U=bool(T <= 1), facet_area=0.5 * R * R,
                        sum_facets=3 * 0.5, sum_sin=3.0)

# explicit hexagon geometry for beta = pi/2 (u_i at 90 deg apart is impossible
# for 3 points summing 3*pi/2 = 4.712 > 2pi? no: sum beta can be up to 2pi).
# u_i are placed so that the pairwise angles at O are beta_i; here symmetric:
u = np.stack([[1.0, np.cos(b), np.cos(2 * b)],
              [0.0, np.sin(b), np.sin(2 * b)]])
print('u=', u)
C = []
for (i, j) in [(0, 1), (1, 2), (2, 0)]:
    M = 0.5 * (u[:, i] + u[:, j])
    d = np.linalg.norm(M)
    s = np.sqrt(max(T ** 2 - d ** 2, 0.0))
    dv = u[:, j] - u[:, i]
    perp = np.array([-dv[1], dv[0]])
    perp = perp / np.linalg.norm(perp)
    C.append(M + s * perp)
C = np.array(C).T
walk = np.array([u[:, 0], C[:, 0], u[:, 1], C[:, 1], u[:, 2], C[:, 2]]).T
x, y = walk[0], walk[1]
sa = 0.5 * float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y))
sl = [float(np.linalg.norm(walk[:, (k + 1) % 6] - walk[:, k])) for k in range(6)]
out['hexagon_pi2'] = dict(signed_area=sa, side_lengths=sl, side_max=max(sl),
                          sum_sq=sum(v * v for v in sl),
                          hexagon_bound=0.25 / np.tan(PI / 6) * sum(v * v for v in sl),
                          T=T, six_tri_sum=None)

# The six triangle areas with apex O:
tri = [(0, 0, 1), (0, 1, 0), (1, 1, 2), (1, 2, 1), (2, 2, 0), (2, 0, 2)]


def a2(p, q, r):
    return 0.5 * float(np.cross(q - p, r - p))


# (triangle k has vertices O, u_i, C_k) etc -- use the walk order
segs = [(u[:, 0], C[:, 0]), (C[:, 0], u[:, 1]), (u[:, 1], C[:, 1]),
        (C[:, 1], u[:, 2]), (u[:, 2], C[:, 2]), (C[:, 2], u[:, 0])]
areas = [a2(np.zeros(2), p, q) for p, q in segs]
out['hexagon_pi2']['six_areas'] = areas
out['hexagon_pi2']['sum_six'] = float(sum(areas))
out['hexagon_pi2']['sum_facet_triangle_areas'] = 3 * 0.5 * R * R * np.sin(b)
out['hexagon_pi2']['note'] = ('facet area (O,u_i,u_j) for beta=pi/2 is 0.5 each; '
                              'the walk area is the same number only if the '
                              'C_k are the TRUE facet circumcenters with T_k<=U')

print(json.dumps(out, indent=1))
with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\reconcile_cap.json", 'w') as f:
    json.dump(out, f, indent=1)
