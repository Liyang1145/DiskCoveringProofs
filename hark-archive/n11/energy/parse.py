#!/usr/bin/env python3
"""Parse the WIP Lean sources (read-only) into energy/parsed.json.
Exact rationals are kept as "num/den" strings."""
import re, json, os, sys
from fractions import Fraction as F
W = '/workspace/work/dcp-n11-lean/wip/lean/N11Formalization'
OUT = '/workspace/work/dcp-n11-lean/energy/parsed.json'

def rd(n): return open(os.path.join(W, n), encoding='utf-8').read()

def ids_in_bang(s):  # ![1,2,3]
    return [int(x) for x in s.strip().strip('![]').split(',') if x.strip()]

# --- tree ---
def parse_tree():
    s = rd('DBMSourceTreeData.lean')
    nodes = {}
    for m in re.finditer(r'def node(\d+) : Node 5011 where\s+db := !\[(.*?)\]\]\s+terminal := (\w+)\s+i := (\d+)\s+j := (\d+)\s+m := (-?\d+)\s+left := (\d+)\s+right := (\d+)', s, re.S):
        n = int(m.group(1))
        rows = re.findall(r'!\[([^\[\]]*)\]', '![' + m.group(2) + ']]')
        db = [[int(x) for x in r.split(',')] for r in rows]
        assert len(db) == 10 and all(len(r) == 10 for r in db), n
        nodes[n] = dict(db=db, terminal=m.group(3) == 'true', i=int(m.group(4)), j=int(m.group(5)),
                        m=int(m.group(6)), left=int(m.group(7)), right=int(m.group(8)))
    assert len(nodes) == 5011, len(nodes)
    # check data binding: data maps index n -> node n ?
    return [nodes[i] for i in range(5011)]

RATRE = r'\(\((-?\d+) : ℚ\)/(\d+)\)|\((-?\d+) : ℚ\)|\((-?\d+) : ℤ\)|\.(tangent|decreasing|left|right)'
def toks(s):
    out = []
    for m in re.finditer(RATRE, s):
        if m.group(1) is not None: out.append(F(int(m.group(1)), int(m.group(2))))
        elif m.group(3) is not None: out.append(F(int(m.group(3))))
        elif m.group(4) is not None: out.append(('int', int(m.group(4))))
        else: out.append(('rule', m.group(5)))
    return out

def parse_line_list(tk):
    lines = []
    assert len(tk) % 8 == 0
    for i in range(0, len(tk), 8):
        a, b, s_, c, t, e, sh, rule = tk[i:i+8]
        lines.append(dict(a=a, b=b, s=s_, c=c, t=t, e=e, shift=sh[1], rule=rule[1]))
    return lines

def parse_G(fname):
    s = rd(fname)
    nid = ids_in_bang(re.search(r'def nodeID : Case → Fin 5011 := (!\[[^\]]*\])', s).group(1))
    pk = []
    for m in re.finditer(r'def packet(\d+) : Packet := ⟨(\d+),(.*?)⟩\n', s, re.S):
        body = m.group(3)
        # split: beta ![...],![lines],![rowFrom],![rowTo],![lam],rmin
        bi = body.index('],![⟨')
        beta = toks(body[:bi+1]); rest = body[bi+2:]
        li = rest.index('⟩],![')
        lines = parse_line_list(toks(rest[:li+2])); rest = rest[li+3:]
        ar = re.match(r'!\[([^\]]*)\],!\[([^\]]*)\],(.*)$', rest, re.S)
        rf = [int(x) for x in ar.group(1).split(',')]; rt = [int(x) for x in ar.group(2).split(',')]
        tl = toks(ar.group(3)); lam = tl[:-1]; rmin = tl[-1]
        assert len(beta) == 16 and len(lines) == 36 and len(lam) == len(rf) == len(rt), (fname, m.group(1))
        pk.append(dict(nodeID=int(m.group(2)), beta=beta, line=lines, rowFrom=rf, rowTo=rt, lam=lam, rmin=rmin))
    assert [p['nodeID'] for p in pk] == nid, fname
    return pk

def parse_B22():
    s = rd('Paid16Batch22Packet.lean')
    def grab(name):
        return re.search(r'def ' + name + r' : [^\n]*?:= (.*)\n', s).group(1)
    nid = ids_in_bang(grab('nodeID'))
    beta = toks(grab('beta')); lam = toks(grab('lam')); rmin = toks(grab('rmin'))
    rf = [ids_in_bang(x) for x in re.findall(r'!\[[\d,]+\]', grab('rowFrom'))]
    rt = [ids_in_bang(x) for x in re.findall(r'!\[[\d,]+\]', grab('rowTo'))]
    lines = parse_line_list(toks(grab('packet')))
    n = len(nid); R = len(rf[0])
    out = []
    for i in range(n):
        out.append(dict(nodeID=nid[i], beta=beta[16*i:16*i+16], line=lines[36*i:36*i+36],
                        rowFrom=rf[i], rowTo=rt[i], lam=lam[R*i:R*i+R], rmin=rmin[i]))
    return out

def parse_weights():
    s = rd('RoundedPaid16.lean')
    body = re.search(r'def numerator : Fin 16 → Fin 36 → ℤ := (.*)\n', s).group(1)
    rows = [[int(x) for x in r.split(',')] for r in re.findall(r'!\[([-\d,]+)\]', body)]
    assert len(rows) == 16 and all(len(r) == 36 for r in rows)
    return rows

def parse_ids():
    out = {}
    out['sharp'] = ids_in_bang(re.search(r'def patchID : Fin 120 → Fin 5011 :=\s*(!\[[^\]]*\])', rd('Patch120DomainPacket.lean')).group(1))
    def nid(f):
        return ids_in_bang(re.search(r'def nodeID : [^\n]*?:= (!\[[^\]]*\])', rd(f)).group(1))
    out['common'] = [284, 562, 4348]; out['dispatch_extra'] = [984]
    out['B01'] = [1112, 2166]; out['B02'] = [2162]
    for f in ['Lambda0Batch7Consumer', 'Lambda0TangentChordC01Consumer', 'CuttingPlaneBatch7Consumer']:
        src = rd(f + '.lean')
        m = re.search(r'def nodeID : [^\n]*?:= (!\[[^\]]*\])', src)
        if m: out[f] = ids_in_bang(m.group(1))
        else:
            imp = re.findall(r'import N11Formalization\.(\w+)', src)
            for g in imp:
                try:
                    out[f] = nid(g + '.lean'); break
                except Exception: pass
    out['B06'] = [3436]; out['B07'] = [4179, 4265]; out['B08'] = [4267]
    return out

if __name__ == '__main__':
    tree = parse_tree()
    G = {}
    for k in range(1, 13):
        G['G%02d' % k] = parse_G('Paid16GeneralG%02d.lean' % k)
    B22 = parse_B22()
    ids = parse_ids()
    wts = parse_weights()
    def enc(x):
        if isinstance(x, F): return '%d/%d' % (x.numerator, x.denominator)
        if isinstance(x, dict): return {k: enc(v) for k, v in x.items()}
        if isinstance(x, list): return [enc(v) for v in x]
        return x
    d = dict(tree=tree, G=enc(G), B22=enc(B22), ids=ids, weights=wts)
    tmp = OUT + '.tmp'; json.dump(d, open(tmp, 'w')); os.replace(tmp, OUT)
    term = [i for i, n in enumerate(tree) if n['terminal']]
    paid = set()
    for k, v in ids.items():
        if k != 'sharp': paid |= set(v)
    for g in G.values(): paid |= {p['nodeID'] for p in g}
    paid |= {p['nodeID'] for p in B22}
    print('terminals', len(term), 'sharp', len(set(ids['sharp'])), 'paid', len(paid),
          {k: len(v) for k, v in ids.items()})
    print('paid all terminal', all(tree[i]['terminal'] for i in paid), 'sharp terminal', all(tree[i]['terminal'] for i in ids['sharp']))
    rem = [i for i in term if i not in paid and i not in set(ids['sharp'])]
    print('remaining', len(rem))
    json.dump(dict(terminals=term, paid=sorted(paid), sharp=sorted(ids['sharp']), remaining=rem),
              open('/workspace/work/dcp-n11-lean/energy/ids.json', 'w'))
