"""Exact Fraction transcription of the WIP face plane DIRECT leaf and PlaneOutside:
SharedMomentFacePlaneDirectCertificate.{planeLinearCell,planeDirectUpperQ}, SharedMomentFacePlaneCertificate.{planeDomainCell,PlaneOutside},
SharedMomentFactorIntervalCertificate.{faceQuadraticCell,faceLinearCell}, SharedMomentFactorRationalNodes.sumThreeInterval.
Gradient leaves (planeGradientUpperQ) are NOT transcribed (direct-only trees)."""
from fractions import Fraction as F
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent))
from switch_kernel import ofRat,add,mul,sinCell,squareCell,maximumQ
PI_LO=F(314159265358979323846,10**20); PI_HI=F(314159265358979323847,10**20)
TWO_R2=2*F(19,50)**2
def sumThree(p,I): return add(add(mul(ofRat(p[0]),I[0]),mul(ofRat(p[1]),I[1])),mul(ofRat(p[2]),I[2]))
def planeDomainCell(B): return [B[0],B[1],(max(F(0),PI_LO-B[0][1]-B[1][1]),min(PI_HI,PI_HI-B[0][0]-B[1][0]))]
def planeLinearCell(p,B): return sumThree([p[0]-p[2],p[1]-p[2],p[2]],[B[0],B[1],(PI_LO,PI_HI)])
def faceQuadraticCell(q,C):
  s=[sinCell(c) for c in C]
  return add(mul(mul(mul(ofRat(TWO_R2),s[0]),s[1]),s[2]),sumThree(q,[squareCell(x) for x in s]))
def faceLinearCell(b,C): return sumThree(b,[sinCell(c) for c in C])
def planeDirectUpperQ(p,q,b,B):
  C=planeDomainCell(B)
  return planeLinearCell(p,B)[1]+maximumQ(faceQuadraticCell(q,C)[1],faceLinearCell(b,C)[1])
def planeOutside(B): return PI_HI<=B[0][0]+B[1][0]
ROOT=((F(0),F(1571,500)),(F(0),F(1571,500)))
def gen_tree(c,M,max_nodes=400000,min_width=F(1,10**6)):
  leaves=[]; stack=[ROOT]; n=0
  while stack:
    B=stack.pop(); n+=1
    if n>max_nodes: return None,n
    if planeOutside(B): leaves.append(('out',B)); continue
    if planeDirectUpperQ(c['p'],c['q'],c['b'],B)<=M: leaves.append(('dir',B)); continue
    k=0 if (B[0][1]-B[0][0])>=(B[1][1]-B[1][0]) else 1
    if B[k][1]-B[k][0]<min_width: return None,n
    m=(B[k][0]+B[k][1])/2
    L=list(B); R=list(B); L[k]=(B[k][0],m); R[k]=(m,B[k][1])
    stack.append(tuple(R)); stack.append(tuple(L))
  return leaves,n

# ---- gradient plane leaf (SharedMomentFacePlaneGradientCertificate.planeGradientUpperQ), exact transcription
from fractions import Fraction as _F
from math import factorial as _fac
_F28=_F(_fac(28)); _FACE=[_F(_fac(2*k)) for k in range(14)]
def cosTQ14(q):
  s=_F(0); q2=q*q; p=_F(1)
  for k in range(14):
    s+= (p/_FACE[k]) if k%2==0 else -(p/_FACE[k]); p*=q2
  return s
def cosLo(q): return cosTQ14(q)-abs(q)**28/_F28
def cosHi(q): return cosTQ14(q)+abs(q)**28/_F28
def _mid(I): return (I[0]+I[1])/2
def _hw(I): return (I[1]-I[0])/2
def cosCell(I): return (max(_F(-1),cosLo(_mid(I))-_hw(I)),min(_F(1),cosHi(_mid(I))+_hw(I)))
def sub(A,B): return (A[0]-B[1],A[1]-B[0])
NEXT=[1,2,0]; PREV=[2,0,1]
def planeCell(B): return [B[0],B[1],(PI_LO-B[0][1]-B[1][1],PI_HI-B[0][0]-B[1][0])]
def planeMidpointCell(B):
  m0=_mid(B[0]); m1=_mid(B[1]); return [ofRat(m0),ofRat(m1),(PI_LO-m0-m1,PI_HI-m0-m1)]
def faceAngleLinearCell(p,C): return sumThree(p,C)
def faceDirectUpperQ(p,q,b,C): return faceAngleLinearCell(p,C)[1]+maximumQ(faceQuadraticCell(q,C)[1],faceLinearCell(b,C)[1])
def faceQuadraticGradientCell(q,C,s):
  return add(mul(mul(mul(ofRat(TWO_R2),cosCell(C[s])),sinCell(C[NEXT[s]])),sinCell(C[PREV[s]])),mul(mul(ofRat(2*q[s]),sinCell(C[s])),cosCell(C[s])))
def faceGradientCell(p,q,b,C,Y,s):
  return add(add(ofRat(p[s]),mul(faceQuadraticGradientCell(q,C,s),squareCell(Y))),mul(mul(ofRat(b[s]),cosCell(C[s])),Y))
def lowerArgQ(A,B):
  if A<0 and 0<B and B< -2*A: return -B/(2*A)
  return _F(1) if 0<A+B else _F(0)
def upperArgQ(A,B):
  if A<0 and 0<B and B< -2*A: return -B/(2*A)
  return _F(0) if A+B<0 else _F(1)
def faceRadiusCell(q,b,C):
  Qc=faceQuadraticCell(q,C); Lc=faceLinearCell(b,C)
  return (lowerArgQ(Qc[0],Lc[0]),upperArgQ(Qc[1],Lc[1]))
def absBoundQ(I): return max(abs(I[0]),abs(I[1]))
def planeGradientUpperQ(p,q,b,B):
  Y=faceRadiusCell(q,b,planeDomainCell(B)); PC=planeCell(B)
  g2=faceGradientCell(p,q,b,PC,Y,2)
  err=sum(absBoundQ(sub(faceGradientCell(p,q,b,PC,Y,i),g2))*_hw(B[i]) for i in range(2))
  return faceDirectUpperQ(p,q,b,planeMidpointCell(B))+err
def gen_tree_grad(c,M,max_nodes=400000,min_width=_F(1,10**6)):
  leaves=[]; stack=[ROOT]; n=0
  while stack:
    B=stack.pop(); n+=1
    if n>max_nodes: return None,n
    if planeOutside(B): leaves.append(('out',B)); continue
    if planeDirectUpperQ(c['p'],c['q'],c['b'],B)<=M: leaves.append(('dir',B)); continue
    if planeGradientUpperQ(c['p'],c['q'],c['b'],B)<=M: leaves.append(('grad',B)); continue
    k=0 if (B[0][1]-B[0][0])>=(B[1][1]-B[1][0]) else 1
    if B[k][1]-B[k][0]<min_width: return None,n
    m=(B[k][0]+B[k][1])/2
    L=list(B); R=list(B); L[k]=(B[k][0],m); R[k]=(m,B[k][1])
    stack.append(tuple(R)); stack.append(tuple(L))
  return leaves,n
