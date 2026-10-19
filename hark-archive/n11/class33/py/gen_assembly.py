"""Emit Class33<Tab>Assembly.lean (DRAFT, uncompiled): the `faces` field (identities + face-tree certificates)
of a FiniteCanonicalCertificate, and the reduction  sectors + strict -> class table.
Usage: gen_assembly.py q0m2 | rep7"""
import json, sys, os
from fractions import Fraction as F
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent; OUT = ROOT / 'lean' / 'N11Formalization'
sys.path.insert(0, str(Path(__file__).parent)); import rep_tables as RT
def code(e): return sum(2 ** i for i in e)
CFG = {
 'q0m2': dict(start=0, k=2, cls='q0', Mod='Q0M2', FS='q0Faces 2', FC='q0FaceCard 2', eta='0', etanonneg='le_refl 0',
              sw='q0m2Switches', swmax='q0m2SwitchMax', ns='Class33Q0M2Assembly', imp='N11Formalization.Class33SwitchFields',
              target='Q0FiniteTable 2', desc='class q0_degree4 (q0Faces 2, hub degrees (4,9))'),
 'rep1': dict(start=2, k=1, cls='q1bal', Mod='Rep1', FS='q1Faces 1 4', FC='q1FaceCard 1 4', eta='rep1Eta', etanonneg='rep1_eta_nonneg',
              sw='rep1Switches', swmax='rep1SwitchMax', ns='Class33Rep1Assembly', imp='N11Formalization.Class33SwitchFields',
              target='CanonicalBalancedFiniteClassCertificate.RepresentativeFiniteTable 1',
              desc='q1-balanced representative cut 1 (q1Faces 1 4)'),
 'rep7': dict(start=0, k=7, cls='q1bal', Mod='Rep7', FS='q1Faces 7 4', FC='q1FaceCard 7 4', eta='rep7Eta', etanonneg='rep7_eta_nonneg',
              sw='rep7Switches', swmax='rep7SwitchMax', ns='Class33Rep7Assembly', imp='N11Formalization.Class33SwitchBridge',
              target='CanonicalBalancedFiniteClassCertificate.RepresentativeFiniteTable 7',
              desc='q1-balanced representative cut 7 (q1Faces 7 4)')}
tab = sys.argv[1]; C = CFG[tab]; M_ = C['Mod']
d = json.loads((ROOT / 'data' / f'face_trees_{tab}.json').read_text())
T = RT.build(C['start'], C['k'], C['cls']); faces = sorted(T['faces'])
assert all(d.get(','.join(map(str, f)), {}).get('ok') for f in faces)
def fs(f): return '{' + ','.join(map(str, f)) + '}'
def mod(f): return f'N11Formalization.Class33FaceTree{M_}F{"_".join(map(str, f))}'
o = [f'import {C["imp"]}', 'import N11Formalization.Class33Labels', 'import N11Formalization.CanonicalBalancedFiniteClassCertificate']
o += [f'import {mod(f)}' for f in faces]
o += ['', f'''/-! Class33 DRAFT (uncompiled): {C["desc"]}.
Faces: 11 plane trees (Class33FaceTree{M_}F*); switches: `{C["sw"]}`.
`{tab}_table_of_sectors` reduces `{C["target"]}` to the 9 sector certificates and the strict total. -/''',
      'set_option autoImplicit false', 'noncomputable section', f'namespace N11Formalization.{C["ns"]}',
      'open CanonicalSharedMomentFiniteCertificate ActualCanonicalSharedMomentConsumer ActualCanonicalMomentTransport',
      'open ActualOrderedMetricGraphs ActualCanonicalFaceCoordinates SharedMomentFiniteFactorCertificate',
      'open SharedMomentEfficientFactorCertificate Class33RepData Class33SwitchBridge Class33Labels', '']
if tab != 'rep7': o.insert(len(o) - 1, 'open Class33SwitchFields')
o.append(f'theorem {tab}_face_cases : ∀ f ∈ {C["FS"]}, ' + ' ∨ '.join(f'f = ({fs(f)} : Finset (Fin 11))' for f in faces) + ' := by\n  decide')
o.append(f'def {tab}FaceMaxCode : ℕ → ℚ')
for f in faces: o.append(f'  | {code(f)} => {mod(f)}.fc_bound')
o.append('  | _ => 0')
o.append(f'def {tab}FaceMax (f : {C["FS"]}) : ℚ := {tab}FaceMaxCode (edgeCode f.val)\n')
for f in faces:
    a, b, c = f; M = mod(f); nm = '_'.join(map(str, f))
    ec = [code(sorted(set(f) - {x})) for x in f]
    o.append(f'''theorem face{nm}_coeff (h : ({fs(f)} : Finset (Fin 11)) ∈ {C["FS"]}) :
    canonicalFaceP {tab}D {tab}Kap ⟨_,h⟩ = {M}.fc_p ∧ canonicalFaceQ {tab}D ⟨_,h⟩ = {M}.fc_q ∧
    canonicalFaceB {tab}D ⟨_,h⟩ = {M}.fc_b ∧ {tab}FaceMax ⟨_,h⟩ = {M}.fc_bound := by
  have h3 := {C["FC"]} ⟨({fs(f)} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({fs(f)} : Finset (Fin 11)) h3 0 = {a} := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({fs(f)} : Finset (Fin 11)) h3 2 = {c} := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({fs(f)} : Finset (Fin 11)) h3 1 = {b} :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({fs(f)} : Finset (Fin 11)).erase {a}) = {ec[0]} := by decide
  have e1 : edgeCode (({fs(f)} : Finset (Fin 11)).erase {b}) = {ec[1]} := by decide
  have e2 : edgeCode (({fs(f)} : Finset (Fin 11)).erase {c}) = {ec[2]} := by decide
  have c3 : edgeCode ({fs(f)} : Finset (Fin 11)) = {code(f)} := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,{tab}D,{tab}Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [{tab}MuN,{tab}KapCode,{M}.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,{tab}D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [{tab}MaskCode,{tab}MinusPairs,{tab}SideSecondCode,{M}.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,{tab}D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [{tab}MaskCode,{tab}MinusPairs,{tab}SideFirstCode,{M}.fc_b]
  · simp only [{tab}FaceMax,c3,{tab}FaceMaxCode]
''')
o.append(f'''/-- The `faces` field. -/
def {tab}Faces : ∀ f : {C["FS"]}, EfficientFaceCertificate (canonicalFaceP {tab}D {tab}Kap f)
    (canonicalFaceQ {tab}D f) (canonicalFaceB {tab}D f) ({tab}FaceMax f) := by
  rintro ⟨f,hf⟩
  rcases {tab}_face_cases f hf with ''' + ' | '.join('rfl' for _ in faces))
for f in faces:
    nm = '_'.join(map(str, f))
    o.append(f'''  · obtain ⟨h1,h2,h3,h4⟩ := face{nm}_coeff hf
    rw [h1,h2,h3,h4]
    exact {mod(f)}.certificate''')
body = f'''{{ faceMax := {tab}FaceMax
      switchMax := {C["swmax"]}
      sectorMax := sectorMax
      balance := {tab}_balance
      edge_nonnegative := {tab}_kap_nonneg
      eta_nonnegative := {C["etanonneg"]}
      bracket := sharpAlpha_bracket
      faces := {tab}Faces
      switches := {C["sw"]}
      sectors := hsector
      strict := hstrict }}'''
wit = f'⟨{tab}D,{tab}Kap,⟨{body}⟩⟩' if tab == 'q0m2' else f'⟨{tab}D,{tab}Kap,{C["eta"]},⟨{body}⟩⟩'
o.append(f'''
/-- Reduction of `{C["target"]}` to its nine sector certificates and the strict total. -/
theorem {tab}_table_of_sectors (sectorMax : Fin 9 → ℚ)
    (hsector : ∀ i : Fin 9, EfficientSectorCertificate (canonicalSectorC {tab}D 0 {C["eta"]} i)
      ({tab}D.mu (ActualRingLinkBoundaryData.nextSite i)) ({tab}D.leftSecond i) ({tab}D.rightSecond i)
      ({tab}D.leftFirst i) ({tab}D.rightFirst i) (sectorMax i))
    (hstrict : canonicalTotalUpperQ {tab}D {tab}Kap {C["eta"]} sharpAlpha {tab}FaceMax {C["swmax"]} sectorMax <
      RatInterval.piLo) : {C["target"]} :=
  {wit}

end N11Formalization.{C["ns"]}
#print axioms N11Formalization.{C["ns"]}.{tab}Faces
#print axioms N11Formalization.{C["ns"]}.{tab}_table_of_sectors''')
p = OUT / f'{C["ns"]}.lean'; t = str(p) + '.tmp'; Path(t).write_text('\n'.join(o) + '\n'); os.replace(t, p)
print('ok', tab, len(faces))
