import re,sys
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent)); import face_kernel as FK
W=Path('/workspace/work/dcp-n11-lean/wip/lean/N11Formalization')
d=(W/'SharedMomentConcreteFace1Data.lean').read_text()
def vec(n):
  m=re.search(rf'def {n} : Fin 3 → ℚ := !\[(.*?)\]\n',d).group(1); return [F(x.strip()) for x in re.findall(r'\(([^()]*?) : ℚ\)',m)]
p,q,b=vec('start0_face1_p'),vec('start0_face1_q'),vec('start0_face1_b'); M=F(18011,100000)
src=''.join((W/f'SharedMomentConcreteFace1Part{i}.lean').read_text() for i in range(4)).replace('\r','')
pat=re.compile(r'\(planeBox \((.*?) : ℚ\) \((.*?) : ℚ\) \((.*?) : ℚ\) \((.*?) : ℚ\)\) := by\n  apply Certificate.accept\n  unfold start0_face1_leaf\n((?:  apply Or\.in[lr]\n)+)')
nd=no=0;bad=0;negfail=0
for m in pat.finditer(src):
  B=((F(m.group(1)),F(m.group(2))),(F(m.group(3)),F(m.group(4)))); ors=m.group(5).split()
  ors=[x for x in ors if x.startswith('Or')]
  if ors==['Or.inl','Or.inr']:
    nd+=1; ok=FK.planeDirectUpperQ(p,q,b,B)<=M; bad+= (not ok)
    negfail+= FK.planeDirectUpperQ(p,q,b,B)<=M-F(1,100)
  elif ors==['Or.inl','Or.inl','Or.inl']:
    no+=1; bad+=(not FK.planeOutside(B))
print('direct leaves',nd,'outside leaves',no,'failures',bad,'neg-control still-accepting (should be < direct)',negfail)
