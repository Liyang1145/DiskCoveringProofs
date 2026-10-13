"""R20-TC-IV3-PROBE (r20-gluing, cline2/DS v4.1f): SOURCE-LEVEL audit of the `lambdify` compile
step used by `r20_tc_iv1.py` / `r20_tc_iv2.py`.

Audited questions (user instruction: check rational constants + pi interval handling):
  Q1  which names does the generated Python source use, and does it ever emit a NON-DYADIC
      float literal (which a point-interval backend would then treat as exact)?
  Q2  is the name `pi` emitted at all in the 5 residuals / 35 first partials / 245 second
      partials, i.e. was the `pi` entry of the module dict ever exercised?
  Q3  what does the current mapping do if a `pi` DOES survive printing (control expression)?
      (`iv_modules()` maps 'pi' -> a 0-argument FUNCTION, see r20_tc_iv1.py line 78-80)
  Q4  exact endpoints: does mpmath 1.3 `ivmpf.a` return an mpf (as the old diagnostics assumed)?

Read-only outside this directory.  Run:
    py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_iv3_probe.py
"""
import json
import re
from fractions import Fraction
from pathlib import Path

import sympy as sp
from mpmath import iv, mp, mpf

from r20_tc_iv1 import symbolic_res5, iv_modules

HERE = Path(__file__).parent
NUM = re.compile(r'(?<![\w.])[0-9]+\.[0-9]+(?:[eE][-+]?[0-9]+)?|(?<![\w.])[0-9]+(?:[eE][-+]?[0-9]+)(?![\w])')


def dyadic(tok):
    try:
        f = float(tok)
    except ValueError:
        return None
    fr = Fraction(f)
    return fr.denominator & (fr.denominator - 1) == 0


def main():
    iv.dps = 40
    exprs, vs = symbolic_res5()
    mods = iv_modules()
    print('=== R20-TC-IV3-PROBE: lambdify source / constant audit ===')
    print('sympy %s  mpmath %s' % (sp.__version__, __import__('mpmath').__version__))

    # ---- build the whole compiled family exactly as iv1/iv2 do
    fam = {}
    for m in range(5):
        fam['f%d' % (m + 1)] = sp.lambdify(vs, exprs[m], modules=mods)
        for i in range(7):
            fam['f%d.d%d' % (m + 1, i)] = sp.lambdify(vs, sp.diff(exprs[m], vs[i]), modules=mods)
            for j in range(7):
                fam['f%d.d%d%d' % (m + 1, i, j)] = sp.lambdify(
                    vs, sp.diff(exprs[m], vs[i], vs[j]), modules=mods)
    print('compiled expressions: %d (5 residual + 35 first + 245 second)' % len(fam))

    # ---- Q1/Q2 census
    pi_hits, non_dyadic, all_toks = [], [], {}
    for k, fn in sorted(fam.items()):
        src = fn.__doc__ or ''
        body = src.split('Source code:')[-1]
        if re.search(r'(?<![\w.])pi(?![\w])', body):
            pi_hits.append(k)
        for tok in NUM.findall(body):
            all_toks[tok] = all_toks.get(tok, 0) + 1
            if not dyadic(tok):
                non_dyadic.append((k, tok))
    print()
    print('Q1/Q2  expressions whose generated source mentions `pi`: %d %s' % (len(pi_hits), pi_hits))
    print('       non-dyadic float literals in any generated source: %d %s'
          % (len(non_dyadic), non_dyadic[:10]))
    print('       distinct numeric literal tokens: %s' % sorted(all_toks))

    # ---- Q3 control: force a surviving pi
    X = vs[0]
    ctrl_bare = sp.lambdify(X, X * sp.pi + sp.sin(sp.pi - 2 * X), modules=mods)
    print()
    print('Q3     control expression  x*pi + sin(pi - 2x)  generated source:')
    csrc = (ctrl_bare.__doc__ or '').split('Source code:')[-1].strip().splitlines()
    print('       %s' % [l.strip() for l in csrc if 'return' in l or 'def ' in l])
    verdict = {}
    try:
        v = ctrl_bare(iv.mpf([1, 2]))
        verdict['old_mapping_call'] = str(v)
        print('       old mapping, value at x=[1,2]: %s  <-- %s'
              % (iv.nstr(v, 12), 'looks like an enclosure' if hasattr(v, 'a') else 'NOT an interval'))
    except Exception as e:
        verdict['old_mapping_call'] = '%s: %s' % (type(e).__name__, e)
        print('       old mapping RAISES %s: %s' % (type(e).__name__, e))
    # fixed mapping: 'pi' is the interval VALUE, not a function
    mods2 = dict(mods)
    mods2['pi'] = iv.pi
    ctrl2 = sp.lambdify(X, X * sp.pi + sp.sin(sp.pi - 2 * X), modules=mods2)
    v2 = ctrl2(iv.mpf([1, 2]))
    print('       fixed mapping (pi -> iv.pi scalar), value at x=[1,2]: %s' % iv.nstr(v2, 20))
    # semantic check of the fixed mapping: sin(pi - 2x) == sin(2x) as interval, x*pi contains pi
    v3 = sp.lambdify(X, X * sp.pi, modules=mods2)(iv.mpf(1))
    print('       control x=1:  x*pi -> %s   (must contain pi = 3.14159265358979...)'
          % iv.nstr(v3, 22))

    # ---- Q4 endpoint accessor semantics
    a = iv.mpf([1, 2])
    q4 = {'a_type': type(a.a).__name__, 'a_a_mpi': str(a.a._mpi_),
          'mpf_of_nondeg_raises': None, 'cmp_undecided_returns': None}
    try:
        mpf(a)
    except Exception as e:
        q4['mpf_of_nondeg_raises'] = '%s: %s' % (type(e).__name__, e)
    q4['cmp_undecided_returns'] = repr(iv.mpf([-1, 2]) > 0.5)
    print()
    print('Q4     ivmpf.a type=%s (a.a==a: %s); mpf(iv[1,2]) -> %s; (iv[-1,2] > 0.5) -> %s'
          % (q4['a_type'], a.a == a, q4['mpf_of_nondeg_raises'], q4['cmp_undecided_returns']))
    print('       => endpoint access via .a/.b is a DEGENERATE ivmpf, not an mpf; comparisons on')
    print('          non-degenerate intervals can return None (undecided) and are silently falsy.')

    out = {'compiled': len(fam), 'pi_in_source': pi_hits, 'non_dyadic_literals': non_dyadic[:20],
           'literal_census': all_toks,
           'control_source': (ctrl_bare.__doc__ or ''),
           'control_old_mapping': verdict, 'control_fixed_mapping': iv.nstr(v2, 25),
           'control_x1_pi': iv.nstr(v3, 25), 'q4': q4}

    # ---- Q5: box endpoint audit -- the iv2 line-70 construction vs the exact box
    import json as _json
    from mpmath import mp as mp_
    LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
    dd = _json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())['certificate']
    ch, rh = dd['center_hex'], dd['radius_hex']
    radf = float.fromhex(rh)
    rad = Fraction(radf)

    def fr(x):
        t = x._mpi_[0] if hasattr(x, '_mpi_') else x._mpf_     # degenerate ivmpf or mpf
        s, m, e, b = t
        v = Fraction(m) * Fraction(2) ** e
        return -v if s else v

    def endpoint_defects(lo, hi, c_i):
        """(outward enlargement, inward shrinkage) of [lo,hi] vs [c_i-rad, c_i+rad]"""
        tlo, thi = c_i - rad, c_i + rad
        return (max(tlo - fr(lo), fr(hi) - thi), max(fr(lo) - tlo, thi - fr(hi)))

    print()
    print('Q5     box endpoint audit: iv2 line-70 construction  mpf(c) +- mpf(rad)  at mp.dps = %d'
          % mp_.dps)
    w_out = w_in = Fraction(0)
    for h in ch:
        c_i = Fraction(float.fromhex(h))
        lo = mpf(c_i.numerator) / mpf(c_i.denominator) - mpf(radf)      # mpf arithmetic (iv2)
        hi = mpf(c_i.numerator) / mpf(c_i.denominator) + mpf(radf)
        o, i_ = endpoint_defects(lo, hi, c_i)
        w_out, w_in = max(w_out, o), max(w_in, i_)
    print('       max OUTWARD enlargement = %s   (box larger than the true box)' % (float(w_out),))
    print('       max INWARD  shrinkage   = %s   (= %.2e of the 1e-9 radius: UNSOUND endpoint)'
          % (float(w_in), float(w_in) / float(rad)))
    iv.dps = 40
    w_out2 = w_in2 = Fraction(0)
    bad = []
    for i, h in enumerate(ch):
        c_i = Fraction(float.fromhex(h))
        U = iv.mpf(float.fromhex(h)) + iv.mpf([-radf, radf])             # iv-only (lead's fix)
        o, i_ = endpoint_defects(U.a, U.b, c_i)
        w_out2, w_in2 = max(w_out2, o), max(w_in2, i_)
        if o > 0 or i_ > 0:
            bad.append(i)
    print('       iv-only construction (iv.mpf(float)+iv.mpf([-rad,rad])): outward = %s , inward = %s'
          % (float(w_out2), float(w_in2)))
    print('       => iv-only box is EXACTLY the true box at all 12 coordinates: %s'
          % (not bad))
    out['box_audit'] = dict(mp_dps_at_iv2_construction=int(mp_.dps),
                            iv2_max_outward=float(w_out), iv2_max_inward=float(w_in),
                            iv2_inward_relative_to_radius=float(w_in) / float(rad),
                            ivonly_max_outward=float(w_out2), ivonly_max_inward=float(w_in2),
                            ivonly_coords_inexact=bad)
    (HERE / 'r20_tc_iv3_probe.json').write_text(json.dumps(out, indent=1, default=str))
    print()
    print('saved r20_tc_iv3_probe.json')


if __name__ == '__main__':
    main()
