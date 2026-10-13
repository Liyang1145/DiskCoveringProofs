"""R20-G: the MINIMAL missing coupling candidate -- holonomy (cycle) conditions of the
shared-side matching system, which the per-row dualization does not impose.

At fixed angles the 21 shared-side equalities are LINEAR in the 20 log-radii
(11 faces + 9 switches):
    log rho_{node1} + log sin(theta_1) = log rho_{node2} + log sin(theta_2)
i.e.  M log rho = rhs,  M (21x20) the signed incidence of the 20-node graph
(faces + switches), rhs the log-sin difference.  The graph is connected, so
rank M = 19 generically and the LEFT null space has dimension 2: exactly two
scalar consistency conditions on the angles (E - V + 1 = 21 - 20 + 1 = 2, cf.
lead/ANGLE-ONLY-EXACT-MODEL.md).  These are necessary for every genuine cover,
are NOT among the 29 dualized factor constraints (dualization is per row), and are
the smallest possible addition (two scalars).

Calibration: at the saved genuine candidate the two conditions hold to machine
precision; they are measured at the high-value combination of the saved 29-factor
solution.  Diagnostic only.
"""
import json, math
import numpy as np
from pathlib import Path
from r20_factor_probe import Model, PI, maximize_all
from r20_residuals import assemble
from r20_mechanism import candidate_point

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'


def build(m):
    """rows: node1, node2 and the log-sin atom for each of the 21 site-site edges."""
    faces = m.faces
    rows = []
    for ei, e in enumerate(m.edges):
        ad = m.adj[e]
        t1, v1 = ad[0]; n1 = t1
        if len(ad) == 2:
            t2, v2 = ad[1]; n2 = t2
        else:
            bi = next(b for b in range(9) if {b, (b + 1) % 9} == set(e)); n2 = 11 + bi
        rows.append((ei, n1, n2, ad))
    return rows


def matvec(m, rows, ang, bsw):
    n = 20
    M = np.zeros((len(rows), n)); rhs = np.zeros(len(rows))
    for r, (ei, n1, n2, ad) in enumerate(rows):
        M[r, n1] += 1.0; M[r, n2] -= 1.0
        t1, v1 = ad[0]; a1 = ang[t1, m.faces[t1].index(v1)]
        if len(ad) == 2:
            t2, v2 = ad[1]; a2 = ang[t2, m.faces[t2].index(v2)]
        else:
            bi = n2 - 11; a2 = bsw[bi]
        rhs[r] = math.log(math.sin(a2)) - math.log(math.sin(a1))
    return M, rhs


def defect(M, rhs, tol=1e-9):
    U, s, Vt = np.linalg.svd(M)
    ns = int(np.sum(s > max(s[0] * 1e-12, 1e-14)))
    Unull = U[:, ns:]                      # left null space, dimension 21 - rank
    proj = Unull.T @ rhs
    sol, res, rk, sv = np.linalg.lstsq(M, rhs, rcond=None)
    return dict(rank=int(ns), left_null_dim=int(M.shape[0] - ns),
                consistency_defect=float(np.linalg.norm(proj)),
                consistency_defect_max=float(np.abs(proj).max()),
                lstsq_residual=float(np.linalg.norm(res) if len(res) else 0.0),
                singular_values=[float(x) for x in s])


def main():
    R = 19 / 50
    m = Model('q0_lower375_dual_0_4.json', R)
    rows = build(m)
    fac = maximize_all(m, 'c825_R38')
    F, ang, yface, bsw, ysw, rng = assemble(m, fac)
    M, rhs = matvec(m, rows, ang, bsw)
    d_arg = defect(M, rhs)
    angc, yfc, bc, ysc, rngc, rc, rho = candidate_point(R)
    Mc, rhsc = matvec(m, rows, angc, bc)
    d_cand = defect(Mc, rhsc)
    # also: angles of the argmax but b replaced by the closure-determined values
    print('ARGMAX  :', {k: (round(v, 6) if isinstance(v, float) else v) for k, v in d_arg.items()
                        if k != 'singular_values'})
    print('CANDIDATE:', {k: (round(v, 8) if isinstance(v, float) else v) for k, v in d_cand.items()
                         if k != 'singular_values'})
    print('singular values M (argmax angles):', [round(x, 4) for x in d_arg['singular_values']])
    print('singular values M (candidate ang):', [round(x, 4) for x in d_cand['singular_values']])
    out = dict(R=R, argmax=d_arg, candidate=d_cand,
               singular_argmax=d_arg['singular_values'],
               singular_candidate=d_cand['singular_values'],
               rhs_argmax=rhs.tolist())
    (HERE / 'r20_holonomy.json').write_text(json.dumps(out, indent=1))
    print('written', HERE / 'r20_holonomy.json')


if __name__ == '__main__':
    main()
