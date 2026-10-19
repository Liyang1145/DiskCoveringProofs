"""Emit core-Lean replays of generated sector trees.  usage: gen_core_sector.py <tag> [LIM leaves per part]
Class33Core/SecTrees/<Mod>S<i>{Base,P<k>,}.lean ; pure pre-validation (NOT credit)."""
import json, sys, os
from fractions import Fraction as F
from pathlib import Path
ROOT = Path('/workspace/work/dcp-n11-lean/class33'); OUT = ROOT / 'lean-core' / 'Class33Core' / 'SecTrees'; OUT.mkdir(parents=True, exist_ok=True)
PIHI = F(314159265358979323847, 10**20)
def q(x):
    x = F(x); return f'({x.numerator}/{x.denominator} : Rat)' if x.denominator != 1 else f'({x.numerator} : Rat)'
def wr(p, s):
    t = str(p) + '.tmp'; open(t, 'w').write(s); os.replace(t, p)
def boxlit(b): return '⟨' + ','.join(q(x) for ab in b for x in ab) + '⟩'
def tok(t):
    if t[0] == 'S': return f'.S {t[1]} {q(t[2])}'
    if t[0] == 'L': return '.L ' + ' '.join(q(x) for x in t[1:])
    return '.P'
def parse(toks):
    """returns tree nodes: ('L',tok) | ('S',dim,t,left,right) with leaf counts"""
    pos = 0
    def rec():
        nonlocal pos
        t = toks[pos]; pos += 1
        if t[0] == 'L': return ['L', t, 1]
        L = rec(); R = rec()
        return ['S', t, L, R, L[-1] + R[-1]]
    r = rec(); assert pos == len(toks); return r
def split(B, d, t):
    L = list(B); R = list(B); lo, hi = B[d]; L[d] = (lo, t); R[d] = (t, hi); return tuple(L), tuple(R)
def flatten(n, out):
    if n[0] == 'L': out.append(n[1])
    else: out.append(n[1]); flatten(n[2], out); flatten(n[3], out)
def partition(n, B, LIM, parts, skel):
    if n[-1] <= LIM:
        parts.append((B, n)); skel.append(['P']); return
    skel.append(n[1]); L, R = split(B, n[1][1], n[1][2])
    partition(n[2], L, LIM, parts, skel); partition(n[3], R, LIM, parts, skel)
def fix(toks):
    out = []
    for t in toks:
        if t[0] == 'S': out.append(['S', t[1], F(t[2])])
        elif t[0] == 'L': out.append(['L'] + [F(x) for x in t[1:]])
        else: out.append(t)
    return out
def emit(name, co, M, toks, LIM=100):
    tree = parse(fix(toks)); root = ((F(0), PIHI), (F(0), F(1)), (F(0), F(1)))
    parts = []; skel = []; partition(tree, root, LIM, parts, skel)
    cov = '⟨' + ','.join(q(co[k]) for k in ('C', 'mu', 'dL', 'dR', 'bL', 'bR')) + '⟩'
    base = (f'import Class33Core.SectorKernel\n/- core-Lean pre-validation, NOT credit: sector tree {name} -/\nnamespace Class33Core.SecTrees.{name}\n'
            f'open Class33Core.SectorKernel\ndef co : Co := {cov}\ndef M : Rat := {q(M)}\ndef root : Box := {boxlit(root)}\nend Class33Core.SecTrees.{name}\n')
    wr(OUT / f'{name}Base.lean', base); mods = [f'{name}Base']
    for k, (B, n) in enumerate(parts):
        fl = []; flatten(n, fl)
        s = (f'import Class33Core.SecTrees.{name}Base\nnamespace Class33Core.SecTrees.{name}.P{k}\nopen Class33Core.SectorKernel Class33Core.SecTrees.{name}\n'
             f'def box : Box := {boxlit(B)}\ndef toks : List Tok := [{",".join(tok(t) for t in fl)}]\n'
             f'theorem ok : chkAll co M box toks [] = true := by decide +kernel\nend Class33Core.SecTrees.{name}.P{k}\n')
        wr(OUT / f'{name}P{k}.lean', s); mods.append(f'{name}P{k}')
    agg = ''.join(f'import Class33Core.SecTrees.{name}P{k}\n' for k in range(len(parts))) + f'import Class33Core.SecTrees.{name}Base\n'
    agg += (f'/- core-Lean pre-validation, NOT credit: skeleton ({len(skel)} nodes) + {len(parts)} parts; '
            f'{sum(p[1][-1] for p in parts)} leaves; root covers sectorRoot (a up to piHi). -/\nnamespace Class33Core.SecTrees.{name}\nopen Class33Core.SectorKernel\n')
    agg += f'def partBoxes : List Box := [{",".join(f"P{k}.box" for k in range(len(parts)))}]\n'
    agg += f'def skel : List Tok := [{",".join(tok(t) for t in skel)}]\n'
    agg += f'theorem skel_ok : chkAll co M root skel partBoxes = true := by decide +kernel\nend Class33Core.SecTrees.{name}\n'
    wr(OUT / f'{name}.lean', agg); mods.append(name)
    return mods, len(parts), len(skel)
if __name__ == '__main__':
    tag = sys.argv[1]; LIM = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    Mod = {'q0m2': 'Q0M2', 'rep7': 'Rep7', 'rep1': 'Rep1'}[tag]
    sel = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else range(9)
    d = json.load(open(ROOT / 'data' / {'q0m2': 'q0_m2.json', 'rep7': 'rep_k7.json', 'rep1': 'rep_k1.json'}[tag]))
    Ms = json.load(open(ROOT / 'data' / f'sector_M_{tag}.json'))
    allm = []
    for i in sel:
        st = json.load(open(ROOT / 'data' / f'sector_{tag}_{i}.state.json')); assert st['done']
        mods, np_, ns = emit(f'{Mod}Sec{i}', d['sectors'][str(i)], F(Ms[str(i)]), st['tokens'], LIM)
        print(i, len(mods), 'modules', np_, 'parts', ns, 'skel'); allm += mods
    open(ROOT / 'data' / f'core_sector_modules_{tag}.txt', 'w').write('\n'.join('Class33Core.SecTrees.' + m for m in allm) + '\n')
