#!/usr/bin/env python3
"""Emit core-Lean replay modules for energy/lean-core/EnergyReplay.
  Weights.lean            : RoundedPaid16 numerator table
  Grp/<name>.lean         : nodes + packets + per-packet `validB … = true` (decide +kernel) + ValidQ
  Controls.lean           : negative controls (must evaluate to false)
usage: gen_core.py <groupname> <source: H###|G##> [first] [count]"""
import os, sys, json, re
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
LC = os.path.join(HERE, 'lean-core', 'EnergyReplay'); os.makedirs(os.path.join(LC, 'Grp'), exist_ok=True)
sys.path.insert(0, HERE)
import parse

def q(x):
    if isinstance(x, str):
        a, b = x.split('/'); x = F(int(a), int(b))
    return '(%d : Rat)' % x.numerator if x.denominator == 1 else '((%d : Rat)/%d)' % (x.numerator, x.denominator)
def line(l):
    return '⟨%s,%s,%s,%s,%s,%s,%d,.%s⟩' % (q(l['a']), q(l['b']), q(l['s']), q(l['c']), q(l['t']), q(l['e']), l['shift'], l['rule'])
def packet(p):
    return '⟨%d,[%s],[%s],[%s],[%s],[%s],%s⟩' % (p['nodeID'], ','.join(q(b) for b in p['beta']),
        ','.join(line(l) for l in p['line']), ','.join(map(str, p['rowFrom'])), ','.join(map(str, p['rowTo'])),
        ','.join(q(x) for x in p['lam']), q(p['rmin']))
def node(nd):
    return '⟨[%s],%s⟩' % (','.join('[%s]' % ','.join(str(x) for x in r) for r in nd['db']), 'true' if nd['terminal'] else 'false')

def atomic(p, t):
    open(p + '.tmp', 'w', encoding='utf-8').write(t); os.replace(p + '.tmp', p)

def weights(parsed):
    rows = ',\n  '.join('[%s]' % ','.join(str(x) for x in r) for r in parsed['weights'])
    t = 'import EnergyReplay.Kernel\nnamespace DCPN11Core.EnergyReplay\n/-- RoundedPaid16.numerator (16×36), transcribed by energy/parse.py. -/\ndef numer : List (List Int) := [\n  %s]\nend DCPN11Core.EnergyReplay\n' % rows
    atomic(os.path.join(LC, 'Weights.lean'), t)

def group(name, pks, tree):
    L = ['import EnergyReplay.Weights', 'namespace DCPN11Core.EnergyReplay.%s' % name, 'open DCPN11Core.EnergyReplay']
    for i, p in enumerate(pks):
        L.append('def node%d : Node := %s' % (i, node(tree[p['nodeID']])))
        L.append('def packet%d : Packet := %s' % (i, packet(p)))
        L.append('theorem ok%d : validB numer node%d packet%d = true := by decide +kernel' % (i, i, i))
        L.append('theorem valid%d : ValidQ numer node%d packet%d := validB_sound ok%d' % (i, i, i, i))
    L.append('end DCPN11Core.EnergyReplay.%s' % name)
    atomic(os.path.join(LC, 'Grp', name + '.lean'), '\n'.join(L) + '\n')

if __name__ == '__main__':
    d = json.load(open(os.path.join(HERE, 'parsed.json')))
    weights(d)
    name, src = sys.argv[1], sys.argv[2]
    first = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    cnt = int(sys.argv[4]) if len(sys.argv) > 4 else 10**9
    if src.startswith('H'):
        parse.W = os.path.join(HERE, 'lean-wip', 'N11Formalization'); pks = parse.parse_G('Paid16General%s.lean' % src)
    else:
        pks = parse.parse_G('Paid16General%s.lean' % src)
    group(name, pks[first:first + cnt], d['tree'])
    print(name, len(pks[first:first + cnt]))

def from_certs(name, nodes):
    d = json.load(open(os.path.join(HERE, 'parsed.json')))
    from checker import load_parsed
    pks = []
    for n in nodes:
        r = json.load(open(os.path.join(HERE, 'certs', '%d.json' % n)))
        p = r['packet']
        def dec(x):
            if isinstance(x, str) and '/' in x:
                a, b = x.split('/'); return F(int(a), int(b))
            if isinstance(x, dict): return {k: dec(v) for k, v in x.items()}
            if isinstance(x, list): return [dec(v) for v in x]
            return x
        pks.append(dec(p))
    group(name, pks, d['tree'])

def controls():
    d = json.load(open(os.path.join(HERE, 'parsed.json')))
    p = parse.parse_G('Paid16GeneralG01.lean')[0]
    import copy
    bad = copy.deepcopy(p); bad['line'][0]['c'] += F(1, 10**6)
    bad2 = copy.deepcopy(p); bad2['rmin'] += F(1, 10)
    L = ['import EnergyReplay.Weights', 'namespace DCPN11Core.EnergyReplay.Controls', 'open DCPN11Core.EnergyReplay',
         'def node0 : Node := %s' % node(d['tree'][p['nodeID']]),
         '/-- G01 packet0 with line 0 intercept raised by 1e-6 (violates the minorant). -/',
         'def badLine : Packet := %s' % packet(bad),
         'theorem badLine_rejected : validB numer node0 badLine = false := by decide +kernel',
         '/-- G01 packet0 with rmin raised by 1/10 (violates reduced cost). -/',
         'def badRmin : Packet := %s' % packet(bad2),
         'theorem badRmin_rejected : validB numer node0 badRmin = false := by decide +kernel',
         'end DCPN11Core.EnergyReplay.Controls']
    atomic(os.path.join(LC, 'Controls.lean'), '\n'.join(L) + '\n')
