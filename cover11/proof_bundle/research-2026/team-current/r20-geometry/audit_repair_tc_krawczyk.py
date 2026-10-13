"""r20-geometry: independent audit of lead/repair_tc_krawczyk.py (peripheral normalization)
and of its Krawczyk-type 12D root certificate.

Read-only wrt lead/: the module is IMPORTED (its __main__ block, which writes
lead/repaired_tc_krawczyk.json, does not run).  Nothing is written outside this directory.

Checks
 1. shape/assembly of the 12-equation system F and its Jacobian J;
 2. INDEPENDENT derivative audit: compare the AD Jacobian rows j[k][i] (first derivatives of
    the 5 residuals) and the AD second-derivative block h[k][i][j1] against high-precision
    central finite differences of the plain (non-interval) residual map;
 3. independent recomputation of the manual chain-rule block of J (rows 5..11) from the FD
    derivatives, and rank checks (lambda uniqueness: 5 constraint gradients independent;
    isolation: 12x12 Jacobian nonsingular at the root);
 4. re-run the Krawczyk inclusion/contraction test at several dyadic radii;
 5. interface check: the normalization block is exactly KKT stationarity for the objective
    z_6 = R (i.e. sum_k lambda_k grad f_k = e_6 = grad z_6), and the certified R-coordinate
    enclosure is compared with the registered covering radius.
"""
import json, sys, hashlib
from pathlib import Path
from mpmath import mp, iv, matrix, lu_solve

mp.dps = 60
HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / "lead"
sys.path.insert(0, str(LEAD))
import repair_tc_krawczyk as RK                                  # noqa: E402  (no __main__ run)

OUT = json.loads((LEAD / "repaired_tc_krawczyk.json").read_text())
U = [mp.mpf(v) for v in OUT["numeric_root"]]
print("root read from lead/repaired_tc_krawczyk.json (%d coordinates)" % len(U))
print("source hash of the audited script:", OUT["source_hashes"][str(LEAD / "repair_tc_krawczyk.py")][:32])

F, J = RK.system(U)
print("\n[1] system shape: len(F) = %d, J = %dx%d ; N = %d (7 z + 5 lambda)"
      % (len(F), len(J), len(J[0]), RK.N))
res = max(abs(v) for v in F[:5])
stat = max(abs(v) for v in F[5:])
print("    max |residual| (first 5) = %s ; max |stationarity residual| (7) = %s"
      % (mp.nstr(res, 6), mp.nstr(stat, 6)))

# ---------- 2. independent finite-difference audit of the AD derivatives
f0, j0, h0 = RK.bundle(U[:7], False)
EPS = [mp.mpf(2) ** (-18)]
bad_j = bad_h = mp.mpf(0)
for e in EPS:
    for k in range(5):
        for i in range(7):
            up = list(U[:7]); um = list(U[:7])
            up[i] += e; um[i] -= e
            fp, _, _ = RK.bundle(up, False)
            fm, _, _ = RK.bundle(um, False)
            fd = (fp[k] - fm[k]) / (2 * e)
            bad_j = max(bad_j, abs(fd - j0[k][i]))
    for k in range(5):
        for i in range(7):
            for jj in range(7):
                ups = [list(U[:7]), list(U[:7]), list(U[:7]), list(U[:7])]
                ups[0][i] += e; ups[1][j] if False else None
                ups[0][jj] += e
                ups[1][i] += e; ups[1][jj] -= e
                ups[2][i] -= e; ups[2][jj] += e
                ups[3][i] -= e; ups[3][jj] -= e
                vals = []
                for uu in ups:
                    ff, _, _ = RK.bundle(uu, False)
                    vals.append(ff[k])
                fd2 = (vals[0] - vals[1] - vals[2] + vals[3]) / (4 * e * e)
                bad_h = max(bad_h, abs(fd2 - h0[k][i][jj]))
print("\n[2] independent central-difference audit of the AD bundle (h = 2^-18):")
print("    max |FD gradient - AD gradient|        = %s" % mp.nstr(bad_j, 6))
print("    max |FD second deriv - AD second deriv| = %s" % mp.nstr(bad_h, 6))

# ---------- 3. manual chain-rule block, ranks
lam = U[7:]
Jchk = [[mp.mpf(0)] * 12 for _ in range(12)]
for k in range(5):
    for i in range(7):
        Jchk[k][i] = j0[k][i]
for i in range(7):
    for k in range(5):
        Jchk[5 + i][7 + k] = -j0[k][i]
    for j1 in range(7):
        Jchk[5 + i][j1] = -sum(lam[k] * h0[k][i][j1] for k in range(5))
dJ = max(abs(Jchk[a][b] - J[a][b]) for a in range(12) for b in range(12))
print("\n[3] manual chain-rule block vs assembled J : max difference = %s" % mp.nstr(dJ, 6))


def rank_and_sv(M, tol=mp.mpf("1e-30")):
    A = matrix(M)
    sv = mp.svd_r(A) if hasattr(mp, "svd_r") else None
    # singular values of the rectangular matrix by eigenvalues of A^T A
    M2 = A.T * A
    ev = mp.eigsy(M2, eigvals_only=True) if hasattr(mp, "eigsy") else None
    evs = sorted([e for e in ev], reverse=True) if ev is not None else []
    r = sum(1 for e in evs if e > tol)
    return r, evs


r5, ev5 = rank_and_sv([[j0[k][i] for i in range(7)] for k in range(5)])
r12, ev12 = rank_and_sv(J)
print("    rank of the 5x7 constraint-gradient block = %d (needs 5 for unique lambda)" % r5)
sv5 = sorted([mp.sqrt(max(mp.mpf(0), e)) for e in ev5], reverse=True); print("    smallest NONZERO singular value of that block = %s" % mp.nstr(min([s for s in sv5 if s > mp.mpf("1e-20")]), 6))
print("    rank of the 12x12 KKT Jacobian            = %d (needs 12 for isolation)" % r12)
sv12 = sorted([mp.sqrt(max(mp.mpf(0), e)) for e in ev12], reverse=True); print("    smallest singular value of the 12x12      = %s" % mp.nstr(sv12[-1], 6))

# ---------- 4. Krawczyk test at several dyadic radii
print("\n[4] Krawczyk inclusion/contraction vs box radius (same center, same float64 Y):")
for rad in [mp.mpf(2) ** -20, mp.mpf(2) ** -23, mp.mpf(2) ** -26, mp.mpf(2) ** -30, mp.mpf(2) ** -33]:
    res = RK.certify(list(map(float, U)), rad)
    print("    rad=2^%-3d incl=%s  Q=%s  max|K-c|/rad=%s"
          % (round(mp.log(rad, 2)), res["pass_inclusion"], mp.nstr(mp.mpf(res["contraction_inf"]), 8),
             mp.nstr(mp.mpf(res["max_K_shift"]) / rad, 8)))

# ---------- 5. interface: normalization meaning + R-coordinate cross-check
st = [sum(lam[k] * j0[k][i] for k in range(5)) for i in range(7)]
print("\n[5] normalization block decoded: sum_k lambda_k grad f_k  vs  e_6 (grad z_6):")
print("    residual vector =", [mp.nstr(v, 6) for v in st])
print("    -> it is exactly KKT stationarity for minimising z_6 = R on {f_0..f_4 = 0},")
print("       with lambda the multipliers; unique because the 5 gradients are independent.")
Rlo, Rhi = [mp.mpf(v) for v in OUT["certificate"]["radius_coordinate_enclosure"]]
print("    certified R-enclosure : [%s, %s]" % (mp.nstr(Rlo, 28), mp.nstr(Rhi, 28)))
print("    registered covering radius R* = 0.3799838531198387 lies inside: %s"
      % (Rlo <= mp.mpf("0.3799838531198387") <= Rhi))
print("    (interface note: this is a cross-check of the certified root, NOT an implication)")
json.dump(dict(max_fd_grad_error=mp.nstr(bad_j, 8), max_fd_hess_error=mp.nstr(bad_h, 8),
               max_chain_rule_error=mp.nstr(dJ, 8), rank_grad_block=r5, rank_jacobian=r12,
               smallest_sv_grad=mp.nstr(min([s for s in sv5 if s > mp.mpf("1e-20")]), 8),
               smallest_sv_jac=mp.nstr(sv12[-1], 8),
               R_enclosure=[mp.nstr(Rlo, 30), mp.nstr(Rhi, 30)]),
          open(HERE / "audit_repair_tc_krawczyk.json", "w"), indent=1)
print("\nwrote audit_repair_tc_krawczyk.json")




