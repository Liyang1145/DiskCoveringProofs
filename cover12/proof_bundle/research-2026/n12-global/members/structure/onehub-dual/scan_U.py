"""n12 one-hub dual: e-scan at R=U plus instrument controls (numeric only).

Controls:
  * negative control: R = 0.3734, e = 0 -- a k=11 style cover numerically
    exists there (11 discs at t=0.715 + centred hub gives R ~ 0.373), so the
    dual MUST NOT return a bound above 11.  A bound <= 11 means the instrument
    is not simply always-excluding.
  * positive control: R = U, e = 0 -- excluded independently by the
    capacity/Jensen lemma, so the dual should give > 11.
"""
import json
import sys
import numpy as np
from onehub_dual_U import run_e, U, EMAX

ROOT = None
try:
    from pathlib import Path
    ROOT = Path(__file__).parent
except Exception:
    pass


def scan(R, es, K, tag):
    rows = []
    for e in es:
        r = run_e(R, e, K)
        rows.append(r)
        print("R=%.6f e=%.5f K=%d  sum_w=%.4f  sup=%.6f  minmax=%.6f  "
              "bound=%.4f  bound/11=%.5f"
              % (R, e, K, r["sum_weights"], r["fine_max_atom"],
                 r["minmax_ratio"], r["rescaled_dual_bound"],
                 r["bound_over_11"]), flush=True)
    json.dump(dict(R=R, K=K, tag=tag, rows=rows),
              open("scan_%s_K%d.json" % (tag, K), "w"), indent=1)
    return rows


if __name__ == "__main__":
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    print("=== e-scan at R = U  (K=%d) ===" % K)
    es = [0.0, 0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08, EMAX]
    scan(U, es, K, "U")
    print("=== negative control: R=0.3734, e=0 (cover exists numerically) ===")
    scan(0.3734, [0.0], K, "negctl")
    print("=== positive control: R=U, e=0 (capacity lemma excludes) ===")
    scan(U, [0.0], K, "posctl")
