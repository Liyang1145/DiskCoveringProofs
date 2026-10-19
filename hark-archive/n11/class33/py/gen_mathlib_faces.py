"""Emit WIP-style (Mathlib) DRAFT face-tree modules in the exact shape of the A25-green
SharedMomentConcreteFace1Part* files (GradientPlaneLeaf, planeBox_split_zero/one, identical norm_num set),
for a table's generated face trees (data/face_trees_<tab>.json), plus per-face `EfficientFaceCertificate`
via FaceCertificate.plane. Usage: gen_mathlib_faces.py <tab> <Mod>.  UNCOMPILED here."""
import json, sys, os, re
from fractions import Fraction as F
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent; OUT = ROOT / 'lean' / 'N11Formalization'
tab, Mod = sys.argv[1], sys.argv[2]
def q(x): x = F(x); return f'({x.numerator}/{x.denominator} : ℚ)' if x.denominator != 1 else f'({x.numerator} : ℚ)'
def wr(p, s):
    t = str(p) + '.tmp'; Path(t).write_text(s); os.replace(t, p)
W = Path('/workspace/work/dcp-n11-lean/wip/lean/N11Formalization')
norm = re.search(r'norm_num \[start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,(.*?)\]', (W / 'SharedMomentConcreteFace1Part0.lean').read_text()).group(1)
d = json.loads((ROOT / 'data' / f'face_trees_{tab}.json').read_text())
for key, r in sorted(d.items()):
    if not r['ok']: continue
    fname = key.replace(',', '_'); ns = f'N11Formalization.Class33FaceTree{Mod}F{fname}'
    leaves = {tuple(F(x) for x in B): kind for kind, B in r['leaves']}
    NL = f'fc_p,fc_q,fc_b,fc_bound,{norm}'
    out = ['import N11Formalization.SharedMomentConcreteFace1Data', 'import N11Formalization.SharedMomentEfficientFactorCertificate', '',
           f'/-! Class33 DRAFT (uncompiled): {tab} face {{{key}}} canonical coefficients, plane tree,',
           f'{len(leaves)} leaves (exact Python pre-validation of every leaf, py/face_kernel.py). -/',
           'set_option autoImplicit false', 'noncomputable section', f'namespace {ns}',
           'open RationalBoxSubdivision SharedMomentFacePlaneGradientCertificate SharedMomentFacePlaneCertificate',
           'open SharedMomentFacePlaneDirectCertificate SharedMomentFactorRationalNodes',
           'open SharedMomentFactorIntervalCertificate SharedMomentFactorLocalGradientCertificate',
           'open RationalTrigLocalLipschitz SharedMomentConcreteFace1', '']
    for x in 'pqb':
        out.append(f'def fc_{x} : Fin 3 → ℚ := ![{",".join(q(v) for v in r["coeff"][x])}]')
    out.append(f'def fc_bound : ℚ := {q(r["M"])}')
    out.append('def fc_leaf (B : Cell (Fin 2)) : Prop :=\n  GradientPlaneLeaf fc_p fc_q fc_b fc_bound B\n')
    cnt = [0]
    def box(B): return f'(planeBox {q(B[0])} {q(B[1])} {q(B[2])} {q(B[3])})'
    def rec(B):
        if B in leaves:
            n = cnt[0]; cnt[0] += 1; kind = leaves[B]
            pre = {'out': '  apply Or.inl\n  apply Or.inl\n  apply Or.inl\n  norm_num [PlaneOutside,planeBox,RatInterval.piHi]',
                   'dir': f'  apply Or.inl\n  apply Or.inr\n  norm_num [{NL}]',
                   'grad': f'  apply Or.inr\n  norm_num [{NL}]'}[kind]
            out.append(f'theorem node_{n} : Certificate fc_leaf\n    {box(B)} := by\n  apply Certificate.accept\n  unfold fc_leaf\n{pre}\n')
            return n
        k = 0 if (B[1] - B[0]) >= (B[3] - B[2]) else 1
        if k == 0:
            m = (B[0] + B[1]) / 2; L = (B[0], m, B[2], B[3]); R = (m, B[1], B[2], B[3])
        else:
            m = (B[2] + B[3]) / 2; L = (B[0], B[1], B[2], m); R = (B[0], B[1], m, B[3])
        a = rec(L); b = rec(R); n = cnt[0]; cnt[0] += 1
        if k == 0:
            out.append(f'theorem node_{n} : Certificate fc_leaf\n    {box(B)} := by\n  exact planeBox_split_zero {q(B[0])} {q(m)} {q(B[1])} {q(B[2])} {q(B[3])} (by norm_num) (by norm_num)\n    node_{a} node_{b}\n')
        else:
            out.append(f'theorem node_{n} : Certificate fc_leaf\n    {box(B)} := by\n  exact planeBox_split_one {q(B[0])} {q(B[1])} {q(B[2])} {q(m)} {q(B[3])} (by norm_num) (by norm_num)\n    node_{a} node_{b}\n')
        return n
    root = rec((F(0), F(1571, 500), F(0), F(1571, 500)))
    out.append(f'''/-- `EfficientFaceCertificate` for this face (FaceCertificate.plane, root as in A25 Face1). -/
def certificate : SharedMomentEfficientFactorCertificate.EfficientFaceCertificate fc_p fc_q fc_b fc_bound :=
  .base (.plane (planeBox (0 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/500 : ℚ))
    (by intro i; fin_cases i <;> norm_num [planeBox,RatInterval.piHi]) node_{root})
end {ns}
#print axioms {ns}.node_{root}''')
    wr(OUT / f'Class33FaceTree{Mod}F{fname}.lean', '\n'.join(out) + '\n')
    print('emitted', key, len(leaves))
