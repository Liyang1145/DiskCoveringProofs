"""cover_forensics.py  (member upper-audit, 2026-09-26)

OBJECT OF THE AUDIT
  The historical output out/cert_<tag>.json (session2/n1314) records
      cover_n_cand      = 364 / 455 / 560 / 680 / 816 / 969 / 1140
      cover_n_uncovered =  36 /  44 /  60 /  72 /  84 / 114 /  142
  while REPORT.md section 3 table records, in the same column ("覆盖正对照"),
      "0 / 328", "0 / 406", "0 / 492", "0 / 602", "0 / 724", "0 / 849", "0 / 986".
  Question: same object? same threshold? which code path produced which number?

METHOD (read-only reuse of the named devices, no file written outside this member dir)
  * configuration = cfg/cert_<tag>.json  key 'centers_dec17' (17-decimal literals)
      -> exact rationals via cert_cand.load_frac_centers(path, key, 17)   [Fraction, no float]
  * threshold     = the `claim` string recorded in out/cert_<tag>.json     [Fraction(str)]
  * candidate family = cert_cand.candidates(C)  (antipodes + bisector-on-circle + circumcentres)
  * four counting definitions, all with d := min_i dist_box_lo(B, c_i) (oriented, sqrt_lo):
      O      = #{B : box_outside_disk(B)}                      (boxes disjoint from D)
      U_all  = #{B : d > claim}                                (NO domain filter)
      U_in   = #{B : d > claim and not box_outside_disk(B)}     (domain filter applied)
      U_out  = #{B : d > claim and box_outside_disk(B)}
  * additionally, a sqrt-free variant using exact rationals:
      q_all  = #{B : (min_i squared axis distance) > claim^2}   (no domain filter)
      q_in   = same, domain filter applied
  * examples = first five offenders in candidate order, printed exactly as the historical
      code did: fstr(d, 20, 'down').

Run:  py -3 -B py/cover_forensics.py > logs/cover_forensics.txt 2>&1
"""
import sys, os, json

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..'))    # workspace root
N1314 = os.path.join(ROOT, 'research-2026', 'session2', 'n1314')
sys.path.insert(0, os.path.join(N1314, 'py'))

from fractions import Fraction as F
import cert_cand
from certlib import dist_box_lo, fstr, box_outside_disk

TAGS = [('n12_othern', 'cert_n12_othern.json'),
        ('n13_v1', 'cert_n13_v1.json'),
        ('n14_v1', 'cert_n14_v1.json'),
        ('n15_v1', 'cert_n15_v1.json'),
        ('n16_v1', 'cert_n16_v1.json'),
        ('n17_v1', 'cert_n17_v1.json'),
        ('n18_v1', 'cert_n18_v1.json')]

REPORT_CHECKED = {'n12_othern': 328, 'n13_v1': 406, 'n14_v1': 492, 'n15_v1': 602,
                  'n16_v1': 724, 'n17_v1': 849, 'n18_v1': 986}


def sq_axis_dist_lo(box, c):
    """exact rational squarish quantity used by dist_box_lo: dx^2 + dy^2 (no sqrt)."""
    (x0, x1), (y0, y1) = box
    cx, cy = c
    dx = F(0) if x0 <= cx <= x1 else min(abs(cx - x0), abs(cx - x1))
    dy = F(0) if y0 <= cy <= y1 else min(abs(cy - y0), abs(cy - y1))
    return dx * dx + dy * dy


def audit_tag(tag, cfgname):
    cfg = os.path.join(N1314, 'cfg', cfgname)
    out = json.load(open(os.path.join(N1314, 'out', 'cert_%s.json' % tag), encoding='utf-8'))
    claim = F(out['claim'])
    C = cert_cand.load_frac_centers(cfg, 'centers_dec17', 17)
    # sanity: literal identity of the Fraction path (17-decimal literal -> exact rational)
    raw = json.load(open(cfg, encoding='utf-8'))['centers_dec17']
    assert len(raw) == len(C), (len(raw), len(C))
    for p, q in zip(raw, C):
        assert F(p[0]) == q[0] and F(p[1]) == q[1], 'literal->Fraction changed a coordinate'
    cand = cert_cand.candidates(C)
    claim2 = claim * claim
    O = 0; U_all = 0; U_in = 0; U_out = 0; q_all = 0; q_in = 0; q_out = 0
    ex_all = []; ex_in = []; ex_out = []
    n_out = 0
    for name, box in cand:
        outside = box_outside_disk(box)
        if outside:
            O += 1
        d = min(dist_box_lo(box, C[i]) for i in range(len(C)))
        if d > claim:
            U_all += 1
            if len(ex_all) < 5:
                ex_all.append([name, fstr(d, 20, 'down')])
            if outside:
                U_out += 1
                if len(ex_out) < 5:
                    ex_out.append([name, fstr(d, 20, 'down')])
            else:
                U_in += 1
                if len(ex_in) < 5:
                    ex_in.append([name, fstr(d, 20, 'down')])
        s2 = min(sq_axis_dist_lo(box, C[i]) for i in range(len(C)))
        if s2 > claim2:
            q_all += 1
            if outside:
                q_out += 1
            else:
                q_in += 1
    print('=== tag %-11s  n=%2d  claim=%s' % (tag, len(C), out['claim']))
    print('    candidates=%d   recorded cover_n_cand=%s   recorded cover_n_uncovered=%s'
          % (len(cand), out['cover_n_cand'], out['cover_n_uncovered']))
    print('    O (boxes disjoint from D)                 = %d' % O)
    print('    U_all (d>claim, no domain filter)         = %d   [recorded uncovered == U_all ? %s]'
          % (U_all, U_all == out['cover_n_uncovered']))
    print('    U_in  (d>claim, box meets D)              = %d' % U_in)
    print('    U_out (d>claim, box disjoint from D)      = %d' % U_out)
    print('    q_all / q_in / q_out (sqrt-free variant)  = %d / %d / %d' % (q_all, q_in, q_out))
    print('    total - O = %d   REPORT.md checked = %s   [match ? %s]'
          % (len(cand) - O, REPORT_CHECKED[tag], len(cand) - O == REPORT_CHECKED[tag]))
    print('    examples(U_all, first5) = %s' % json.dumps(ex_all))
    print('    recorded cover_examples  = %s' % json.dumps(out['cover_examples']))
    print('    examples identical ? %s' % (ex_all == [list(x) for x in out['cover_examples']]))
    if ex_in:
        print('    examples(U_in, first5)  = %s' % json.dumps(ex_in))
    if ex_out:
        print('    examples(U_out, first5) = %s' % json.dumps(ex_out))
    print()


def main():
    print('WORKSPACE  =', ROOT)
    print('n1314 dir  =', N1314)
    print()
    for tag, cfg in TAGS:
        audit_tag(tag, cfg)


if __name__ == '__main__':
    main()
