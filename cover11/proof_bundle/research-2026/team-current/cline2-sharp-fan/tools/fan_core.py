# -*- coding: utf-8 -*-
"""Shared core: load saved certified object, inward-root fan data, mpmath dps=60.

Conventions (caliber):
  unit disk D; 11 equal disks radius R; angles radians; lengths in units of the
  unit-disk radius.
  ring site  j : |c_j| >= 1-R  (touches/brackets bd D)
  hub  site  h : |h|  <  1-R  (strictly interior => covers no point of bd D)
  inward-root representation of a ring disk at argument phi_j:
      b_j = cos t_j - sqrt(R^2 - sin^2 t_j),   t_j = asin(R/b_j)  in [0, asin R]
      sites c_j = b_j * e^{i phi_j};  ring j covers the arc  [phi_j - t_j, phi_j + t_j]
  switch  P_i := inner crossing of bd D, bd B(c_i,R), bd B(c_{i+1},R)
                  (i indexes the CYCLIC ring order), |P_i| = 1.
  owned arc width w_i := angular measure of the part of bd D that ring i owns
                  (nearest-site assignment; equals gap between switches).
"""
import json, os, math

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir, os.pardir, os.pardir, os.pardir))

def load_object(path=None):
    """returns (C, R_float, R_mp) with C = list of (mpf, mpf) at dps=60."""
    import mpmath as mp
    mp.mp.dps = 60
    if path is None:
        path = os.path.join(ROOT, "n11", "upper", "certified_object.json")
    with open(path, "r", encoding="utf-8-sig") as f:
        obj = json.load(f)
    C = [(mp.mpf(int(a)) / mp.mpf(10) ** 17, mp.mpf(int(b)) / mp.mpf(10) ** 17)
         for a, b in obj["centers_scaled_1e17"]]
    iv = obj.get("certified_interval")
    if iv:
        Rlo = mp.mpf(iv["lo"]); Rhi = mp.mpf(iv["hi"])
        R = (Rlo + Rhi) / 2
    else:
        R = mp.mpf("0.379983853119838709048518179573429853811597902801556119905385")
    return C, R, mp


def classify(C, R):
    import mpmath as mp
    mod = [ mp.sqrt(c[0]**2 + c[1]**2) for c in C ]
    ring = [j for j in range(len(C)) if mod[j] + R >= 1]
    hub  = [j for j in range(len(C)) if mod[j] + R <  1]
    return ring, hub, mod


def arg_of(c):
    import mpmath as mp
    return mp.atan2(c[1], c[0])
