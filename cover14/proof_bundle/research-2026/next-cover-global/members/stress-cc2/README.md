# stress-cc2 — which scripts are authoritative (round 2)

READ FIRST: `REPORT.md` (= `REPORT-round2.md`). Round 1 is kept as `REPORT-round1-superseded.md`.

USE THESE
- `py/geom.py` — geometry chain, correct `b = r+sqrt(r^2-((s-z)/2)^2)`
- `py/interface.py` — fixed geometry interface: 14 centres, hash, 16 vertices (14 tight / 2 slack),
  10 anchors, 20 tight edges, 10 gaps, cap-active {4,9} — log `logs/interface_run.txt`
- `py/join.py` — coordinate join vs `lead/n14-actual-vertices-numeric.json` — log `logs/join.txt`
- `py/witness_pos.py` — strictly positive witness balance vectors — log `logs/witness_pos.txt`
- `py/audit_fix2.py` — error tracing for C1157/C1155/C1154 — log `logs/audit_fix2.txt`
- `py/kkt_sign.py` — KKT sign control (`g_k <= c`) and r-factor finite-difference control —
  log `logs/kkt_sign.txt`
- `py/calib.py` — n12 calibration — log `logs/calib.txt`

SUPERSEDED / WRONG (trail only)
- `py/n14v2.py` — KKT constraint signed the wrong way (`g_k >= 0`); its geometry printout is fine.
- `py/n14final.py` — float64 print path + a 1e-50 tightness filter ⇒ spurious "4 anchor edges".
- `py/witness_balance.py`, `py/final_check.py` — SVD null-vector sign misread ⇒ wrong "no positive
  balance" and a wrong forced-zero count.
- `py/step1/step3/step4/step5/step6*.py` — geometry before the `b` fix.
- `py/n14kkt*.py`, `py/n14cone.py`, `py/n14hess*.py`, `py/n14curv.py` — torque-sign / gap
  parameterisation errors.

Carried-over facts owned elsewhere: the six-face support mechanism and the curvature numbers are the
Lead's (`lead/STRESS-SUPPORT-ANALYTIC.md`, `stress_barycentric.py`, `stress-schur-probe.json`,
`stress-curvature-control.json`); this directory only confirms them numerically (retraction C1154 →
C1166).
