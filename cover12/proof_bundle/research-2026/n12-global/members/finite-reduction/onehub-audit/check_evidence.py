#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_evidence.py -- record-level checks of the lead's k11 and near-merge evidence:
hashes, exact binary-rational fields, displayed constants, per-segment readings.
Read-only."""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

N12 = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent / "out"
OUT.mkdir(exist_ok=True)
Uq = F('0.361102963744508672616920293904')
DEL = F(1, 20)
U_half_widths = 1


def interval_of(s):
    lo, hi = s.strip("[]").split(",")
    return F(lo), F(hi)


def main():
    rep, chk = {}, {}
    k11 = json.loads((N12 / "evidence" / "onehub-interval-all.json").read_text(encoding="utf-8"))
    nm1 = json.loads((N12 / "evidence" / "nearmerge-interval-1-20.json").read_text(encoding="utf-8"))
    nm2 = json.loads((N12 / "evidence" / "nearmerge-interval-1-20-tail.json").read_text(encoding="utf-8"))

    # ---- hashes ----
    rep["k11_kernel_sha256_recorded"] = k11.get("kernel_sha256")
    rep["k11_kernel_sha256_mine"] = hashlib.sha256(
        (N12 / "lead" / "onehub_interval_certificate.py").read_bytes()).hexdigest()
    chk["k11_kernel_hash_matches_current_source"] = (
        k11.get("kernel_sha256") == rep["k11_kernel_sha256_mine"])
    rep["k11_input_sha256_recorded"] = k11.get("input_sha256")
    rep["k11_input_sha256_mine"] = hashlib.sha256(
        (N12 / "members" / "structure" / "onehub-dual" / "segment_U_K1.json").read_bytes()).hexdigest()
    chk["k11_input_hash_matches_current_input"] = (
        k11.get("input_sha256") == rep["k11_input_sha256_mine"])
    rep["k11_dps"] = k11.get("mpmath_iv_dps")
    chk["k11_dps_30"] = (k11.get("mpmath_iv_dps") == 30)

    # ---- exact fields consistent with the printed intervals ----
    ok_ex = True
    rows = []
    for s in k11["segments"]:
        lo, hi = interval_of(s["upper"])
        ue = F(s["upper_exact"])
        tlo, thi = interval_of(s["target"])
        te = F(s["target_lower_exact"])
        ok = (lo <= ue <= hi) and (tlo <= te <= thi) and (ue < te)
        ok_ex &= ok
        rows.append(dict(e=s["e_fraction"], upper_exact_in_printed=bool(lo <= ue <= hi),
                         target_lower_in_printed=bool(tlo <= te <= thi),
                         strict=bool(ue < te), margin=float(te - ue),
                         ring_count=s.get("ring_count")))
    chk["k11_exact_fields_consistent_and_strict"] = bool(ok_ex)
    rep["k11_segments"] = rows

    # ---- near-merge displayed constants ----
    rep["nm_radius_recorded"] = nm1.get("radius")
    rep["nm_radius_exact"] = str(Uq + DEL)
    rep["nm_offset_recorded"] = nm1.get("offset_max")
    rep["nm_offset_exact"] = str(3 * Uq - 1 + DEL)
    chk["nm_radius_matches_U_plus_delta"] = (nm1.get("radius") == str(Uq + DEL))
    chk["nm_offset_matches_3U_1_plus_delta"] = (nm1.get("offset_max") == str(3 * Uq - 1 + DEL))
    rep["nm_assert_4U_1_2d_lt_1"] = str(4 * Uq - 1 + 2 * DEL) + " < 1: " + str(4 * Uq - 1 + 2 * DEL < 1)
    rep["nm_assert_2_4U_d_gt_d"] = str(2 - 4 * Uq - DEL) + " > " + str(DEL) + ": " + str(2 - 4 * Uq - DEL > DEL)
    chk["nm_code_asserts_hold"] = bool(4 * Uq - 1 + 2 * DEL < 1 and 2 - 4 * Uq - DEL > DEL)
    chk["nm_target_ring_count_10"] = (nm1.get("target_ring_count") == 10)

    # ---- near-merge segment readings ----
    segs = list(nm1["segments"]) + list(nm2["segments"])
    strict_ok = (len(segs) == 12)
    rows = []
    for s in segs:
        lo, hi = interval_of(s["upper"])
        tlo, thi = interval_of(s["target"])
        strict = (hi < tlo)
        strict_ok &= strict
        rows.append(dict(e=s["e_fraction"], boxes=s["boxes"], leaves=s["leaves"],
                         upper_hi=str(hi)[:24], target_lo=str(tlo)[:24],
                         margin=float(tlo - hi), strict=bool(strict),
                         ring_count=s.get("ring_count")))
    chk["nm_twelve_segments_strict"] = bool(strict_ok)
    # e-intervals adjacent and covering [0,1]
    eiv = [tuple(F(x) for x in s["e_fraction"]) for s in segs]
    chk["nm_e_intervals_cover_0_1"] = (eiv[0][0] == 0 and eiv[-1][1] == 1 and
                                       all(eiv[i][1] == eiv[i + 1][0] for i in range(11)))
    rep["nm_segments"] = rows
    rep["nm_boxes_total"] = sum(s["boxes"] for s in segs)
    rep["nm_boxes_max"] = max(s["boxes"] for s in segs)

    (OUT / "evidence-checks.json").write_text(json.dumps(rep, indent=1, ensure_ascii=False,
                                                        default=str), encoding="utf-8")
    for k, v in chk.items():
        print("%s  %s" % ("PASS" if v else "FAIL", k))
    print("nm boxes total=%s max=%s" % (rep["nm_boxes_total"], rep["nm_boxes_max"]))
    print("k11 margins (exact):", [round(r["margin"], 10) for r in rep["k11_segments"]])
    print("nm margins:", [("%.3e" % r["margin"]) for r in rep["nm_segments"]])
    print("log ->", OUT / "evidence-checks.json")
    if any(v is False for v in chk.values()):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
