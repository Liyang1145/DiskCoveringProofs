"""Emit Mathlib reflective modules for sector trees (DRAFT, uncompiled in WIP toolchain).
usage: gen_mathlib_sectors.py <tag> [LIM leaves/part=25] [PARTS/group=40] [sectors]
Class33Sec<Mod>S<i>Base (co,M) / G<g> (parts + ok) / aggregator (certificate)."""
import json, sys, os
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, '/workspace/work/dcp-n11-lean/class33/py')
import gen_core_sector as G
ROOT = G.ROOT; OUT = ROOT / 'lean' / 'N11Formalization'
def q(x):
    x = F(x); return f'({x.numerator}/{x.denominator} : ℚ)' if x.denominator != 1 else f'({x.numerator} : ℚ)'
def boxl(b): return '⟨' + ','.join(q(x) for ab in b for x in ab) + '⟩'
def tok(t):
    if t[0] == 'S': return f'.S {t[1]} {q(t[2])}'
    if t[0] == 'L': return '.L ' + ' '.join(q(x) for x in t[1:])
    return '.P'
HEAD = 'set_option autoImplicit false\nnoncomputable section\n'
def emit(Mod, i, co, M, toks, LIM, PG):
    name = f'Class33Sec{Mod}S{i}'
    tree = G.parse(G.fix(toks)); root = ((F(0), G.PIHI), (F(0), F(1)), (F(0), F(1)))
    parts = []; skel = []; G.partition(tree, root, LIM, parts, skel)
    groups = [parts[k:k + PG] for k in range(0, len(parts), PG)]
    cov = '⟨' + ','.join(q(co[k]) for k in ('C', 'mu', 'dL', 'dR', 'bL', 'bR')) + '⟩'
    G.wr(OUT / f'{name}Base.lean', f'import N11Formalization.Class33SectorReflect\n\n/-! Class33 DRAFT (uncompiled): sector {i} of {Mod} coefficients + bound. -/\n{HEAD}namespace N11Formalization.{name}Base\nopen Class33SectorReflect\ndef co : Co := {cov}\ndef M : ℚ := {q(M)}\nend N11Formalization.{name}Base\n')
    mods = [name + 'Base']
    for g, grp in enumerate(groups):
        items = []
        for B, n in grp:
            fl = []; G.flatten(n, fl)
            items.append(f'({boxl(B)}, [{",".join(tok(t) for t in fl)}])')
        s = (f'import N11Formalization.{name}Base\n\n/-! Class33 DRAFT (uncompiled): {len(grp)} parts of sector tree {name}. -/\n{HEAD}namespace N11Formalization.{name}G{g}\nopen Class33SectorReflect\n'
             f'def parts : List (Box × List Tok) := [{",".join(items)}]\n'
             f'theorem ok : partsOK N11Formalization.{name}Base.co N11Formalization.{name}Base.M parts = true := by decide +kernel\nend N11Formalization.{name}G{g}\n')
        G.wr(OUT / f'{name}G{g}.lean', s); mods.append(f'{name}G{g}')
    ng = len(groups)
    allp = ''; 
    expr = f'N11Formalization.{name}G{ng-1}.parts'
    for g in range(ng - 2, -1, -1): expr = f'N11Formalization.{name}G{g}.parts ++ ({expr})'
    imports = ''.join(f'import N11Formalization.{name}G{g}\n' for g in range(ng))
    okl = ','.join(f'N11Formalization.{name}G{g}.ok' for g in range(ng))
    agg = (f'import N11Formalization.Class33SectorReflect\nimport N11Formalization.{name}Base\n{imports}\n/-! Class33 DRAFT (uncompiled): sector tree {name}: skeleton {len(skel)} nodes + {len(parts)} parts, {sum(p[1][-1] for p in parts)} leaves. -/\n{HEAD}'
           f'namespace N11Formalization.{name}\nopen Class33SectorReflect N11Formalization.{name}Base\n'
           f'def allParts : List (Box × List Tok) := {expr}\n'
           f'theorem allOK : partsOK co M allParts = true := by\n  simp only [allParts, partsOK_append, {okl}, Bool.and_self]\n'
           f'def skel : List Tok := [{",".join(tok(t) for t in skel)}]\n'
           f'theorem skel_ok : chkAll co M rootBox skel (allParts.map Prod.fst) = true := by decide +kernel\n'
           f'def certificate : SharedMomentEfficientFactorCertificate.EfficientSectorCertificate co.C co.mu co.dL co.dR co.bL co.bR M :=\n'
           f'  efficient_of_chk co M skel (allParts.map Prod.fst) (partsOK_sound co M allParts allOK) skel_ok\nend N11Formalization.{name}\n#print axioms N11Formalization.{name}.certificate\n')
    G.wr(OUT / f'{name}.lean', agg); mods.append(name)
    return mods
if __name__ == '__main__':
    tag = sys.argv[1]; LIM = int(sys.argv[2]) if len(sys.argv) > 2 else 25; PG = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    sel = [int(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 else range(9)
    Mod = {'q0m2': 'Q0M2', 'rep7': 'Rep7', 'rep1': 'Rep1'}[tag]
    d = json.load(open(ROOT / 'data' / {'q0m2': 'q0_m2.json', 'rep7': 'rep_k7.json', 'rep1': 'rep_k1.json'}[tag]))
    Ms = json.load(open(ROOT / 'data' / f'sector_M_{tag}.json')); allm = []
    for i in sel:
        st = json.load(open(ROOT / 'data' / f'sector_{tag}_{i}.state.json')); assert st['done']
        m = emit(Mod, i, d['sectors'][str(i)], F(Ms[str(i)]), st['tokens'], LIM, PG); print(i, len(m), 'modules'); allm += m
    open(ROOT / 'data' / f'mathlib_sector_modules_{tag}.txt', 'w').write('\n'.join('N11Formalization.' + x for x in allm) + '\n')
