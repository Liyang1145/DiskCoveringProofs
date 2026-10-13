"""repro_improved_upper.py -- member upper (next-cover-global), 2026-09-26.

Independent reproduction of the IMPROVED n=14 upper-bound object produced by lead:

  input   : lead/improved-upper-test.json   (14 centres as EXACT rationals,
            threshold T = 1658660171381170613/5000000000000000000)
  compare : the previously reproduced configuration C411 (its exact squared radius
            q0_old, obtained in members/upper from the literal object).

What this file does (all read-only on the lead assets; writes only under members/upper):
  1. loads the new exact rational centres VERBATIM (pure given-centres: the root
     equations / root-scout are NOT audited here and are not used as premises);
  2. reproduces the covering verdict with the OLD isqrt BOX kernel of
     research-2026/lead/verify_c407_lead.py by importing it and calling
     analyse(C, T, grid=False) -- the old main() is NOT run and nothing is written
     into the old directory;
  3. cross-checks with our own exact rational-algebra kernel (no intervals);
  4. compares EXACTLY T^2 < q0_old (equivalent to T < R(C411)) and reports the
     improvement in radius units.

Run: py -3 -B py/repro_improved_upper.py
"""
import hashlib
import importlib.util as iu
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

try:
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
except Exception:
    pass

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
NEW = ROOT / 'research-2026/next-cover-global/lead/improved-upper-test.json'
SCOUT = ROOT / 'research-2026/next-cover-global/lead/root-scout.json'
SCOUTPY = ROOT / 'research-2026/next-cover-global/lead/root_scout.py'
OLDK = ROOT / 'research-2026/lead/verify_c407_lead.py'
OLDJSON = ROOT / 'research-2026/session2/type14/out/hprec_sol.json'
OUT = HERE.parent / 'logs' / 'improved_upper_result.txt'

LOG = []


def say(s=''):
    print(s)
    LOG.append(s)


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def imp_old_kernel():
    spec = iu.spec_from_file_location('old_box_kernel', str(OLDK))
    mod = iu.module_from_spec(spec)
    spec.loader.exec_module(mod)              # module level defines paths + functions only
    return mod                                # old main() deliberately NOT called


def main():
    say('=== provenance (read-only) ===')
    for nm, p in (('improved-upper-test.json', NEW), ('root-scout.json', SCOUT),
                  ('root_scout.py', SCOUTPY), ('old box kernel verify_c407_lead.py', OLDK),
                  ('C411 literal object hprec_sol.json', OLDJSON)):
        say(f'  {nm:38s} sha256 {sha(p)}')

    js = json.loads(NEW.read_text(encoding='utf-8'))
    C = [(F(a), F(b)) for a, b in js['centers']]
    T = F(js['threshold'])
    assert len(C) == 14
    say()
    say('=== the given object (verbatim, exact rationals) ===')
    say(f'  status            : {js["status"]}')
    say(f'  scope             : {js["scope"]}')
    say(f'  source            : {js["source"]}')
    say(f'  threshold T       : {T} = {js["threshold_decimal"]}')
    say(f'  declared count    : candidate_count={js["candidate_count"]} uncovered={js["uncovered"]}')
    say(f'  centres = 14 exact rationals, first centre:')
    say(f'    ({C[0][0]})')
    say(f'    ({C[0][1]})')
    say(f'  all coords |.| <= 1.3317 (base-domain box): '
        f'{all(abs(v) <= F("1.33173203427623416") for c in C for v in c)}')

    # ---------------------------------------------------- reproduction 1: old box kernel
    say()
    say('=== reproduction 1: OLD isqrt BOX kernel, analyse(C, T, grid=False) ===')
    old_out = ROOT / 'research-2026/lead/c407_lead_result.txt'
    before = (sha(old_out), old_out.stat().st_mtime_ns)
    vk = imp_old_kernel()
    res = vk.analyse(C, T, grid=False)
    after = (sha(old_out), old_out.stat().st_mtime_ns)
    say(f'  old-domain write check: c407_lead_result.txt unchanged = {before == after}'
        f'  (sha {before[0][:16]}…)')
    say(f'  candidates (boxes) = {res["n"]}   uncovered = {len(res["fails"])}'
        + ('' if not res['fails'] else f'   e.g. {res["fails"][:4]}'))
    say(f'  R(C) enclosure (old kernel, 10^-40 directed isqrt) = '
        f'[{float(res["R_lo"]):.20f}, {float(res["R_hi"]):.20f}]')
    say(f'  argmax(lo) = {res["arglo"]}   argmax(hi) = {res["arghi"]}')
    say(f'  verdict: R(C) <= T via the box kernel: {"YES (0 uncovered)" if not res["fails"] else "NO"}')
    say(f'  (grid cross-check skipped: grid=False as instructed)')

    # ---------------------------------------------------- reproduction 2: exact kernel
    say()
    say('=== reproduction 2: our exact rational-algebra kernel (independent of 1) ===')
    spec = iu.spec_from_file_location('exact_kernel', str(HERE / 'repro_c411_independent.py'))
    ek = iu.module_from_spec(spec)
    spec.loader.exec_module(ek)
    P, unc = ek.cover_test(C, T, 'new exact object at T')
    say(f'  T^2 (exact rational) = {T * T}')
    say(f'  verdict: R(C) <= T via exact algebra: {"YES" if not unc else "NO"}')

    # ---------------------------------------------------- exact radius of the new object
    say()
    say('=== exact radius of the NEW object (for the improvement statement) ===')
    q_new, lab_new, p_new, _ = ek.exact_radius(C, 'new object')
    SC = 10 ** 70

    def dec(q):
        m = (q.numerator * 10 ** 140) // q.denominator
        return '0.' + str(math.isqrt(m)).rjust(70, '0')[:70]

    say(f'  argmax candidate = {lab_new}   sqrt(q_new) = {dec(q_new)}')

    # ---------------------------------------------------- exact comparison with C411
    say()
    say('=== exact comparison with the C411 object ===')
    ld = json.loads(OLDJSON.read_text(encoding='utf-8'))
    th = [F(s) for s in ld['th']]
    Cold = []
    for j in (0, 2):
        for s in (-1, 1):
            for t in (-1, 1):
                Cold.append((s * th[j], t * th[j + 1]))
    for j in (4, 5):
        Cold.extend([(th[j], F(0)), (-th[j], F(0))])
    Cold.extend([(F(0), th[6]), (F(0), -th[6])])
    q0_old = None
    # C411 maximiser recomputed exactly (circumcentre of Cold's triple 10,11,12)
    i, j, k = 10, 11, 12
    ax, ay = Cold[j][0] - Cold[i][0], Cold[j][1] - Cold[i][1]
    bx, by = Cold[k][0] - Cold[i][0], Cold[k][1] - Cold[i][1]
    D = ax * by - ay * bx
    e = (Cold[j][0] ** 2 + Cold[j][1] ** 2 - Cold[i][0] ** 2 - Cold[i][1] ** 2) / 2
    f = (Cold[k][0] ** 2 + Cold[k][1] ** 2 - Cold[i][0] ** 2 - Cold[i][1] ** 2) / 2
    ux, uy = (e * by - f * ay) / D, (ax * f - bx * e) / D
    q0_old = min((ux - a) ** 2 + (uy - b) ** 2 for a, b in Cold)
    say(f'  C411 radius   R_old = sqrt(q0_old) = {dec(q0_old)}')
    say(f'  new threshold T                       = {dec(T * T)}')
    say(f'  EXACT: T^2 < q0_old          : {T * T < q0_old}   (<=> T < R_old: the new threshold'
        f' is strictly below the OLD object radius)')
    say(f'  EXACT: q0_old - T^2          = {q0_old - T * T}')
    say(f'  EXACT: T^2 < q_new           : {T * T < q_new}   (= False means T > R_new, which is'
        f' what makes the cover test pass)')
    say(f'  EXACT: q_new < q0_old        : {q_new < q0_old}   (new object strictly better)')
    say(f'  EXACT: q0_old - q_new        = {q0_old - q_new}')
    say(f'  radius improvements (converted with R_old + T etc., not with the squares):')
    ro, rn, tt = math.sqrt(float(q0_old)), math.sqrt(float(q_new)), math.sqrt(float(T * T))
    say(f'    R_old - T     = {float(q0_old - T * T) / (ro + tt):.6e}')
    say(f'    R_old - R_new = {float(q0_old - q_new) / (ro + rn):.6e}')
    say(f'    T - R_new     = {float(T * T - q_new) / (tt + rn):.6e}')
    say(f'  (sanity: these should read ~9.155e-19 for R_old - T, matching the lead statement)')
    sy = json.loads(SCOUT.read_text(encoding='utf-8'))
    try:
        r_scout = sy['z_c_r'][2]
    except Exception:
        r_scout = str(sy)[:80]
    dec_new = dec(q_new)
    say()
    say('  artifact metadata check (root-scout.json z_c_r[2] vs the given object):')
    say(f'    root-scout r string      = {r_scout}')
    say(f'    exact R of given centres = {dec_new}')
    say(f'    identical strings        : {r_scout == dec_new}   '
        f'(root-scout is numeric_only and is NOT used as a premise here)')
    say()
    say('=== verdict ===')
    ok = (not res['fails']) and (not unc) and T * T < q0_old
    say(f'  IMPROVED UPPER BOUND REPRODUCED: {"YES" if ok else "NO"}')
    say(f'  object: the 14 exact rational centres given verbatim in improved-upper-test.json')
    say(f'  (root equations / root-scout NOT audited here and not used as a premise).')
    say(f'  scope: this configuration only; NOT the family minimum, NOT r_D(14), NOT optimality.')
    OUT.write_text('\n'.join(LOG) + '\n', encoding='utf-8')
    print(f'\n[written] {OUT}')


if __name__ == '__main__':
    main()
