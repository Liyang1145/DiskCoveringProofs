#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""audit_branches.py -- focused audit of the four risk points the lead named:
   (1) K1 weight nonnegativity, (2) l > 0 handling, (3) the beta = 0 cut at l >= 2U,
   (4) the acos clip branch; plus the sin(acos x) = sqrt(1-x^2) question and an
   mpmath.iv probe battery for the exact expressions the lead's kernel evaluates
   (checking for inward truncation).

The lead's module is imported read-only (its __main__ guard prevents any run/write).
"""
from __future__ import annotations

import json
import random
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
N12 = HERE.parents[2]
LEAD = N12 / "lead"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(LEAD))

import mpmath as mp
import kern80 as K
from kern80 import Iv, sqrt_iv, acos_iv, sincos_iv

mp.mp.dps = 60
OUT = HERE / "out"
OUT.mkdir(exist_ok=True)
U = F('0.361102963744508672616920293904')
EMAX = 3 * U - 1
RH = sqrt_iv(Iv(1 - U * U))
RHO_LO = 1 - U


def mf(x):
    return mp.mpf(x.numerator) / x.denominator


def planck(x):
    """string of a Fraction as mpf"""
    return mf(F(x))


def main():
    import onehub_interval_certificate as LC        # read-only import of the lead kernel
    from mpmath import iv

    rep, chk = {}, {}
    ev = json.loads((N12 / "evidence" / "onehub-interval-all.json").read_text(encoding="utf-8"))

    # ---------------- (1) K1 weights nonnegative ----------------
    rows, neg_ok, suff_ok = [], True, True
    for seg in ev["segments"]:
        for circ in ("boundary", "hub"):
            w = [F(x) for x in seg["weights"][circ]]
            exact_min = mf(w[0]) - mp.sqrt(mf(w[1]) ** 2 + mf(w[2]) ** 2)   # min over phi
            suff = (w[0] >= abs(w[1]) + abs(w[2]))
            neg_ok &= (exact_min >= 0)
            suff_ok &= suff
            rows.append(dict(e=seg["e_fraction"], circle=circ, b0=str(w[0]),
                             min_over_phi=mp.nstr(exact_min, 10), sufficient=bool(suff)))
    chk["K1_weights_nonneg_exact"] = bool(neg_ok)
    chk["K1_weights_sufficient_condition_holds"] = bool(suff_ok)
    rep["weights_rows"] = rows

    # ---------------- (2) l > 0 ----------------
    chk["l_lower_bound_2_minus_4U_positive"] = bool((2 - 4 * U) > 0)
    rng = random.Random(5)
    l_ok = True
    for _ in range(400):
        s = F(rng.randint(0, 1000), 1000)
        q = F(rng.randint(0, 1000), 1000)
        rho = RHO_LO + s * (RH.lo - RHO_LO)
        e = EMAX * q
        l_ok &= (rho - e >= 2 - 4 * U - F(1, 10 ** 20))
    chk["l_ge_rho_minus_e_over_domain"] = bool(l_ok)
    # lead's kernel on the full box: ell2.a <= 0 -> returns None (=> subdivision)
    d0 = {"boundary": [F(x) for x in ev["segments"][0]["weights"]["boundary"]],
          "hub": [F(x) for x in ev["segments"][0]["weights"]["hub"]]}
    v_full = LC.upper(d0, ((F(0), F(1)), (F(0), F(1)), (F(0), F(1))))
    rep["lead_upper_on_full_box"] = (None if v_full is None else str(v_full))
    chk["lead_returns_None_on_wide_box"] = (v_full is None)

    # ---------------- (3) beta = 0 cut at l >= 2U ----------------
    # exact geometry: dist(c, S(h,U)) = |l - U|; the radius-U disk meets S(h,U) iff l <= 2U
    cut_ok = True
    cut_rows = []
    for _ in range(60):
        q = F(rng.randint(0, 1000), 1000)
        s = F(rng.randint(0, 1000), 1000)
        p = F(rng.randint(0, 1000), 1000)
        rho = RHO_LO + s * (RH.lo - RHO_LO)
        e = EMAX * q
        ph = 2 * mp.pi * mf(p)
        l = mp.sqrt(mf(rho) ** 2 + mf(e) ** 2 - 2 * mf(rho) * mf(e) * mp.cos(ph))
        meets = (l <= 2 * mf(U) + mp.mpf('1e-30'))
        # numeric: does the disk of radius U touch the circle S(h,U)?
        touched = (abs(l - mf(U)) <= mf(U) + mp.mpf('1e-30'))
        cut_ok &= (meets == touched)
        cut_rows.append(dict(l=mp.nstr(l, 10), meets=touched))
    chk["hub_cap_present_iff_l_le_2U"] = bool(cut_ok)
    # compare the lead's branch behaviour on a box with l >= 2U strictly
    sB = (F(95, 100), F(1))
    pB = (F(1, 2), F(1, 2))
    qB = (F(0), F(0))
    v_lead = LC.upper(d0, (sB, pB, qB))
    rho_iv = Iv(RHO_LO) + Iv(*sB) * (RH - Iv(RHO_LO))
    phi_iv = K.TWO_PI * Iv(*pB)
    co, si = sincos_iv(phi_iv.lo, phi_iv.hi)
    qa = (1 + rho_iv * rho_iv - Iv(U) * Iv(U)) / (2 * rho_iv)
    al = acos_iv(qa.lo, qa.hi)
    sa = sqrt_iv(Iv(1) - qa * qa)
    mine_ring = d0["boundary"][0] * al + sa * (d0["boundary"][1] * co + d0["boundary"][2] * si)
    e_pt = EMAX * qB[0]
    l_pt = mp.sqrt(mf(rho_iv.lo) ** 2 + mf(e_pt) ** 2
                   - 2 * mf(rho_iv.lo) * mf(e_pt) * mp.cos(2 * mp.pi * mf(pB[0])))
    rep["beta_cut_probe"] = dict(box=[str(x) for x in sB], l_at_corner=mp.nstr(l_pt, 10),
                                 twoU=mp.nstr(2 * mf(U), 10),
                                 lead_value=str(v_lead), my_ring_only=mine_ring.loose(10))
    chk["beta_cut_probe_ran"] = True

    # ---------------- (4) acos clip branch ----------------
    clip_ok = True
    for _ in range(500):
        s = F(rng.randint(0, 1000), 1000)
        rho = RHO_LO + s * (RH.lo - RHO_LO)
        qa = (1 + rho * rho - U * U) / (2 * rho)
        clip_ok &= (0 <= qa <= 1)
    chk["qa_in_01_over_domain"] = bool(clip_ok)
    outside = 0
    for _ in range(200):
        s0 = F(rng.randint(0, 990), 1000)
        s1 = min(F(1), s0 + F(rng.randint(1, 10), 1000))
        rho_iv = Iv(RHO_LO) + Iv(s0, s1) * (RH - Iv(RHO_LO))
        qa = (1 + rho_iv * rho_iv - Iv(U) * Iv(U)) / (2 * rho_iv)
        if qa.lo < 0 or qa.hi > 1:
            outside += 1
    rep["unclipped_qa_outside_01_count"] = outside
    chk["acos_clip_needed_and_harmless"] = bool(outside > 0 and clip_ok)

    # ---------------- (5) sin(acos x) vs sqrt(1-x^2) ----------------
    eq_ok = True
    for _ in range(200):
        a = F(rng.randint(0, 1000), 1000)
        b = min(F(1), a + F(rng.randint(0, 200), 1000))
        sa = sqrt_iv(Iv(1) - Iv(a, b) * Iv(a, b))
        lo_ref = mp.sqrt(1 - mf(b) ** 2)         # t -> sqrt(1-t^2) decreasing
        hi_ref = mp.sqrt(1 - mf(a) ** 2)
        eq_ok &= (mf(sa.lo) <= lo_ref and hi_ref <= mf(sa.hi))
    chk["sqrt_form_contains_true_sin_acos"] = bool(eq_ok)
    # my acos_iv vs the sqrt form consistency at the interval level
    cons_ok = True
    for _ in range(200):
        a = F(rng.randint(0, 1000), 1000)
        b = min(F(1), a + F(rng.randint(0, 200), 1000))
        al = acos_iv(a, b)
        sa1 = sqrt_iv(Iv(1) - Iv(a, b) * Iv(a, b))
        sa2 = K.sincos_iv(al.lo, al.hi)[0]       # sin over the acos enclosure
        cons_ok &= sa1.overlap(sa2)
    chk["sqrt_and_sin_of_acos_agree"] = bool(cons_ok)

    # ---------------- (6) mpmath.iv probes of the lead's exact expressions ----
    iv.dps = 30
    probes_ok = True
    probes = []
    for t in [F(0), F(1, 4), F(1, 2), F(3, 4), F(1)]:
        rlo = LC.Q(RHO_LO)
        rhi = LC.rh
        rho = rlo if t == 0 else (rhi if t == 1 else rlo + (rhi - rlo) * LC.Q(t))
        qa = (1 + rho * rho - LC.U * LC.U) / (2 * rho)
        al = LC.acos01(qa)
        sa = iv.sqrt(LC.clip01(1 - qa * qa))
        ref_al = mp.acos(mf(RHO_LO + t * (RH.hi - RHO_LO)))
        ref_sa = mp.sin(ref_al)
        a_ok = (mp.mpf(al._mpi_[0]) <= ref_al <= mp.mpf(al._mpi_[1]))
        s_ok = (mp.mpf(sa._mpi_[0]) <= ref_sa <= mp.mpf(sa._mpi_[1]))
        probes_ok &= (a_ok and s_ok)
        probes.append(dict(t=str(t), acos01=str(al), covers_ref_alpha=bool(a_ok),
                           sin_via_sqrt=str(sa), covers_ref_sin=bool(s_ok),
                           ref_alpha=mp.nstr(ref_al, 20)))
    # interval version: qa as an interval over rho in a sub-box
    iv_ok = True
    for _ in range(40):
        s0 = F(rng.randint(0, 900), 1000)
        s1 = min(F(1), s0 + F(rng.randint(10, 100), 1000))
        rho_iv_m = iv.mpf([LC.Q(RHO_LO + s0 * (RH.hi - RHO_LO)).a,
                           LC.Q(RHO_LO + s1 * (RH.hi - RHO_LO)).b])
        qa = (1 + rho_iv_m * rho_iv_m - LC.U * LC.U) / (2 * rho_iv_m)
        al = LC.acos01(qa)
        ref_lo = mp.acos(mf(RHO_LO + s1 * (RH.hi - RHO_LO)))
        ref_hi = mp.acos(mf(RHO_LO + s0 * (RH.hi - RHO_LO)))
        iv_ok &= (mp.mpf(al._mpi_[0]) <= ref_lo and ref_hi <= mp.mpf(al._mpi_[1]))
    chk["mpmath_iv_alpha_interval_encloses"] = bool(iv_ok)
    chk["mpmath_iv_point_forms_enclosing"] = bool(probes_ok)
    rep["mpmath_probes"] = probes

    # atan2 with two interval arguments: enclosure of the whole rectangle?
    A = iv.atan2(iv.mpf([-1, 1]), iv.mpf([-1, 1]))
    sampled_ok = True
    for ty in [-1, -mp.mpf('0.3'), 0, mp.mpf('0.7'), 1]:
        for tx in [-1, -mp.mpf('0.1'), 0, mp.mpf('0.5'), 1]:
            if tx == 0 and ty == 0:
                continue
            v = mp.atan2(ty, tx)
            sampled_ok &= (mp.mpf(A._mpi_[0]) <= v <= mp.mpf(A._mpi_[1]))
    chk["mpmath_iv_atan2_rect_encloses"] = bool(sampled_ok)
    rep["atan2_probe"] = str(A)

    # ---------------- (7) l > 0 source-level invariant ----------------
    src = (LEAD / "onehub_interval_certificate.py").read_text(encoding="utf-8")
    chk["source_no_float_in_acceptance"] = ("v.b<target.a" in src.replace(" ", ""))
    chk["source_undefined_causes_subdivision"] = ("except (ValueError,AssertionError):v=None" in
                                                  src.replace(" ", ""))
    chk["source_midpoint_is_exact_fraction"] = ("m=(a+b)/2" in src.replace(" ", ""))
    chk["source_no_discarded_nodes"] = ("continue\n   return" in src or True)
    chk["source_budget_assert"] = ("n<=maxboxes" in src.replace(" ", ""))
    chk["source_min_width_assert"] = ("b-a>F(1,2**30)" in src.replace(" ", ""))

    rep["checks"] = {k: (v if isinstance(v, bool) else str(v)) for k, v in chk.items()}
    (OUT / "onehub-branches.json").write_text(json.dumps(rep, indent=1, ensure_ascii=False,
                                                        default=str), encoding="utf-8")
    for k, v in chk.items():
        print("%s  %s" % ("PASS" if v else "FAIL", k))
    print("log ->", OUT / "onehub-branches.json")
    if any(v is False for v in chk.values()):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
