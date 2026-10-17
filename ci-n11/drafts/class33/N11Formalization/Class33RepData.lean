import N11Formalization.CanonicalSharedMomentFiniteCertificate

/-! Class33 DRAFT (uncompiled): the two q1-balanced representative canonical tables
q1Faces 7 4 (historical start0) and q1Faces 1 4 (historical start2), instantiated from the 9-place
coefficients of shared_moment_dense_certificate_{0,2}_4.json relabelled ring h -> h-1 (mod 9).
Pre-validated: class33/lean-core/Class33Core/Rep{7,1}.lean (core Lean, compiled) and
class33/py/rep_tables.py (Fractions). Data alone gives no class credit. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33RepData
open ActualCanonicalMomentTransport ActualOrderedMetricGraphs ActualCanonicalFaceCoordinates
open ActualSharedMomentRationalCertificate ActualEdgeFlagSums

/-- Injective code of a label set (used only to tabulate edge-indexed data). -/
def edgeCode (e : Finset (Fin 11)) : ℕ := ∑ i ∈ e, 2 ^ i.val

/-! ### rep7: q1Faces 7 4 (historical start0) -/
def rep7MuN : ℕ → ℚ
  | 0 => (-66337987/1000000000 : ℚ)
  | 1 => (7389693/1000000000 : ℚ)
  | 2 => (-60407023/1000000000 : ℚ)
  | 3 => (-16410659/1000000000 : ℚ)
  | 4 => (24401399/500000000 : ℚ)
  | 5 => (-523273/15625000 : ℚ)
  | 6 => (-55970009/1000000000 : ℚ)
  | 7 => (-11051187/500000000 : ℚ)
  | 8 => (30939859/1000000000 : ℚ)
  | 9 => (-14313377/250000000 : ℚ)
  | 10 => (-18632957/200000000 : ℚ)
  | _ => 0
def rep7SideFirstCode : ℕ → ℚ
  | 3 => (72616089/500000000 : ℚ)
  | 6 => (113801907/500000000 : ℚ)
  | 12 => (23346599/125000000 : ℚ)
  | 24 => (140138273/500000000 : ℚ)
  | 48 => (292226871/1000000000 : ℚ)
  | 96 => (37678367/200000000 : ℚ)
  | 192 => (195588767/1000000000 : ℚ)
  | 257 => (184795967/1000000000 : ℚ)
  | 258 => (541272263/1000000000 : ℚ)
  | 384 => (267616379/1000000000 : ℚ)
  | 514 => (17146697/200000000 : ℚ)
  | 516 => (92876433/1000000000 : ℚ)
  | 520 => (79665267/500000000 : ℚ)
  | 528 => (-81241601/200000000 : ℚ)
  | 768 => (-102151007/500000000 : ℚ)
  | 1040 => (-95823657/500000000 : ℚ)
  | 1056 => (-12049829/100000000 : ℚ)
  | 1088 => (9637047/1000000000 : ℚ)
  | 1152 => (91136367/1000000000 : ℚ)
  | 1280 => (-282727661/1000000000 : ℚ)
  | 1536 => (28580731/250000000 : ℚ)
  | _ => 0
def rep7SideSecondCode : ℕ → ℚ
  | 3 => (-76591199/500000000 : ℚ)
  | 6 => (-126267217/500000000 : ℚ)
  | 12 => (-11822577/50000000 : ℚ)
  | 24 => (-194596841/1000000000 : ℚ)
  | 48 => (-1454237/6250000 : ℚ)
  | 96 => (-64193013/250000000 : ℚ)
  | 192 => (-249270779/1000000000 : ℚ)
  | 257 => (-21538627/125000000 : ℚ)
  | 258 => (-98958367/250000000 : ℚ)
  | 384 => (-212817061/1000000000 : ℚ)
  | 514 => (74532777/1000000000 : ℚ)
  | 516 => (-20008213/500000000 : ℚ)
  | 520 => (-194926973/1000000000 : ℚ)
  | 528 => (289191727/1000000000 : ℚ)
  | 768 => (251843483/1000000000 : ℚ)
  | 1040 => (134582743/1000000000 : ℚ)
  | 1056 => (157259879/1000000000 : ℚ)
  | 1088 => (-7784481/500000000 : ℚ)
  | 1152 => (-3424359/25000000 : ℚ)
  | 1280 => (229784511/1000000000 : ℚ)
  | 1536 => (-25895989/250000000 : ℚ)
  | _ => 0
def rep7KapCode : ℕ → ℚ
  | 3 => (0 : ℚ)
  | 6 => (0 : ℚ)
  | 12 => (0 : ℚ)
  | 24 => (0 : ℚ)
  | 48 => (0 : ℚ)
  | 96 => (0 : ℚ)
  | 192 => (0 : ℚ)
  | 257 => (0 : ℚ)
  | 258 => (0 : ℚ)
  | 384 => (0 : ℚ)
  | 514 => (0 : ℚ)
  | 516 => (0 : ℚ)
  | 520 => (0 : ℚ)
  | 528 => (0 : ℚ)
  | 768 => (0 : ℚ)
  | 1040 => (0 : ℚ)
  | 1056 => (0 : ℚ)
  | 1088 => (0 : ℚ)
  | 1152 => (0 : ℚ)
  | 1280 => (0 : ℚ)
  | 1536 => (0 : ℚ)
  | _ => 0
def rep7LeftFirstN : ℕ → ℚ
  | 0 => (-2154379/1000000000 : ℚ)
  | 1 => (-30343871/100000000 : ℚ)
  | 2 => (77843283/500000000 : ℚ)
  | 3 => (-61016341/1000000000 : ℚ)
  | 4 => (-87590289/200000000 : ℚ)
  | 5 => (-670110993/1000000000 : ℚ)
  | 6 => (173524101/1000000000 : ℚ)
  | 7 => (-8660027/1000000000 : ℚ)
  | 8 => (605467/1000000000 : ℚ)
  | _ => 0
def rep7LeftSecondN : ℕ → ℚ
  | 0 => (50371299/1000000000 : ℚ)
  | 1 => (276655647/1000000000 : ℚ)
  | 2 => (52347527/1000000000 : ℚ)
  | 3 => (-70963859/1000000000 : ℚ)
  | 4 => (17670779/50000000 : ℚ)
  | 5 => (467460643/1000000000 : ℚ)
  | 6 => (7360493/200000000 : ℚ)
  | 7 => (41834891/1000000000 : ℚ)
  | 8 => (-1195057/250000000 : ℚ)
  | _ => 0
def rep7RightFirstN : ℕ → ℚ
  | 0 => (-3817079/1000000000 : ℚ)
  | 1 => (-678791593/1000000000 : ℚ)
  | 2 => (8226689/50000000 : ℚ)
  | 3 => (486889131/1000000000 : ℚ)
  | 4 => (153650861/1000000000 : ℚ)
  | 5 => (-340440453/500000000 : ℚ)
  | 6 => (-153855179/500000000 : ℚ)
  | 7 => (-605467/1000000000 : ℚ)
  | 8 => (-84202849/500000000 : ℚ)
  | _ => 0
def rep7RightSecondN : ℕ → ℚ
  | 0 => (15300071/500000000 : ℚ)
  | 1 => (188303/400000 : ℚ)
  | 2 => (286373/15625000 : ℚ)
  | 3 => (-7565983/20000000 : ℚ)
  | 4 => (765617/15625000 : ℚ)
  | 5 => (23527717/50000000 : ℚ)
  | 6 => (36052173/125000000 : ℚ)
  | 7 => (1195057/250000000 : ℚ)
  | 8 => (60094389/500000000 : ℚ)
  | _ => 0
/-- Face masks: -1 on these (face code, flag-edge code) pairs, +1 otherwise. -/
def rep7MinusPairs : List (ℕ × ℕ) := [(518,514),(524,516),(536,520),(770,258),(1120,1056),(1216,1088),(1408,1152),(1552,528),(1552,1040),(1552,1536),(1792,768),(1792,1280)]
def rep7MaskCode (fc ec : ℕ) : ℤ := if (fc, ec) ∈ rep7MinusPairs then -1 else 1
def rep7D : CanonicalCoeffQ (q1Faces 7 4) where
  faceCard := q1FaceCard 7 4
  mu := fun i => rep7MuN i.val
  faceMask := fun f s =>
    (rep7MaskCode (edgeCode f.val) (edgeCode (f.val.erase (canonicalLabel f.val (q1FaceCard 7 4 f) s))) : ℚ)
  switchMask := fun _ => -1
  sideFirst := fun e => rep7SideFirstCode (edgeCode e)
  sideSecond := fun e => rep7SideSecondCode (edgeCode e)
  leftFirst := fun i => rep7LeftFirstN i.val
  leftSecond := fun i => rep7LeftSecondN i.val
  rightFirst := fun i => rep7RightFirstN i.val
  rightSecond := fun i => rep7RightSecondN i.val
  width := (0 : ℚ)
def rep7Kap : Finset (Fin 11) → ℚ := fun e => rep7KapCode (edgeCode e)
def rep7Eta : ℚ := (13670573/31250000 : ℚ)

/-! ### rep1: q1Faces 1 4 (historical start2) -/
def rep1MuN : ℕ → ℚ
  | 0 => (-17256927/250000000 : ℚ)
  | 1 => (2784343/1000000000 : ℚ)
  | 2 => (66184907/500000000 : ℚ)
  | 3 => (24622919/1000000000 : ℚ)
  | 4 => (-12860411/500000000 : ℚ)
  | 5 => (26964443/1000000000 : ℚ)
  | 6 => (2321277/15625000 : ℚ)
  | 7 => (20685877/1000000000 : ℚ)
  | 8 => (-6446613/500000000 : ℚ)
  | 9 => (37439727/500000000 : ℚ)
  | 10 => (39440233/500000000 : ℚ)
  | _ => 0
def rep1SideFirstCode : ℕ → ℚ
  | 3 => (144785329/1000000000 : ℚ)
  | 6 => (176036609/500000000 : ℚ)
  | 12 => (359958497/1000000000 : ℚ)
  | 24 => (229306291/1000000000 : ℚ)
  | 48 => (240066493/1000000000 : ℚ)
  | 96 => (-21198513/125000000 : ℚ)
  | 192 => (121696337/1000000000 : ℚ)
  | 257 => (2370459/20000000 : ℚ)
  | 258 => (385640331/1000000000 : ℚ)
  | 384 => (51744851/200000000 : ℚ)
  | 516 => (-110612529/250000000 : ℚ)
  | 520 => (-365919637/1000000000 : ℚ)
  | 528 => (-13546947/100000000 : ℚ)
  | 544 => (-61457079/500000000 : ℚ)
  | 576 => (-29429741/62500000 : ℚ)
  | 1026 => (154119593/1000000000 : ℚ)
  | 1028 => (-163450127/500000000 : ℚ)
  | 1088 => (148787259/500000000 : ℚ)
  | 1152 => (-183086511/500000000 : ℚ)
  | 1280 => (1397153/250000000 : ℚ)
  | 1536 => (-342394249/1000000000 : ℚ)
  | _ => 0
def rep1SideSecondCode : ℕ → ℚ
  | 3 => (-164310891/1000000000 : ℚ)
  | 6 => (-26873729/200000000 : ℚ)
  | 12 => (-7061079/62500000 : ℚ)
  | 24 => (-89873677/500000000 : ℚ)
  | 48 => (-47494749/250000000 : ℚ)
  | 96 => (207599217/1000000000 : ℚ)
  | 192 => (3903461/100000000 : ℚ)
  | 257 => (-9419661/62500000 : ℚ)
  | 258 => (-157658899/500000000 : ℚ)
  | 384 => (-203580357/1000000000 : ℚ)
  | 516 => (2688011/10000000 : ℚ)
  | 520 => (10355437/31250000 : ℚ)
  | 528 => (42513927/500000000 : ℚ)
  | 544 => (-62409273/1000000000 : ℚ)
  | 576 => (311569613/1000000000 : ℚ)
  | 1026 => (-75043671/500000000 : ℚ)
  | 1028 => (164353743/1000000000 : ℚ)
  | 1088 => (-22955111/200000000 : ℚ)
  | 1152 => (366859069/1000000000 : ℚ)
  | 1280 => (-6750447/100000000 : ℚ)
  | 1536 => (55294039/250000000 : ℚ)
  | _ => 0
def rep1KapCode : ℕ → ℚ
  | 3 => (0 : ℚ)
  | 6 => (0 : ℚ)
  | 12 => (0 : ℚ)
  | 24 => (0 : ℚ)
  | 48 => (0 : ℚ)
  | 96 => (0 : ℚ)
  | 192 => (0 : ℚ)
  | 257 => (0 : ℚ)
  | 258 => (0 : ℚ)
  | 384 => (0 : ℚ)
  | 516 => (0 : ℚ)
  | 520 => (0 : ℚ)
  | 528 => (0 : ℚ)
  | 544 => (0 : ℚ)
  | 576 => (0 : ℚ)
  | 1026 => (0 : ℚ)
  | 1028 => (0 : ℚ)
  | 1088 => (0 : ℚ)
  | 1152 => (0 : ℚ)
  | 1280 => (0 : ℚ)
  | 1536 => (0 : ℚ)
  | _ => 0
def rep1LeftFirstN : ℕ → ℚ
  | 0 => (22806211/1000000000 : ℚ)
  | 1 => (-188739699/1000000000 : ℚ)
  | 2 => (480821209/1000000000 : ℚ)
  | 3 => (-338628961/200000000 : ℚ)
  | 4 => (-362973421/200000000 : ℚ)
  | 5 => (-266053671/1000000000 : ℚ)
  | 6 => (205913849/500000000 : ℚ)
  | 7 => (-1097045203/1000000000 : ℚ)
  | 8 => (-188390043/1000000000 : ℚ)
  | _ => 0
def rep1LeftSecondN : ℕ → ℚ
  | 0 => (1802223/50000000 : ℚ)
  | 1 => (408351029/1000000000 : ℚ)
  | 2 => (1857941/62500000 : ℚ)
  | 3 => (59129827/50000000 : ℚ)
  | 4 => (623390001/500000000 : ℚ)
  | 5 => (111453653/250000000 : ℚ)
  | 6 => (54848891/500000000 : ℚ)
  | 7 => (38182861/62500000 : ℚ)
  | 8 => (15560333/125000000 : ℚ)
  | _ => 0
def rep1RightFirstN : ℕ → ℚ
  | 0 => (-4674781/40000000 : ℚ)
  | 1 => (-236328581/200000000 : ℚ)
  | 2 => (480821209/1000000000 : ℚ)
  | 3 => (521518357/1000000000 : ℚ)
  | 4 => (-938512807/1000000000 : ℚ)
  | 5 => (-5372589/3906250 : ℚ)
  | 6 => (45241467/100000000 : ℚ)
  | 7 => (188390043/1000000000 : ℚ)
  | 8 => (-23085437/125000000 : ℚ)
  | _ => 0
def rep1RightSecondN : ℕ → ℚ
  | 0 => (109557847/1000000000 : ℚ)
  | 1 => (917698247/1000000000 : ℚ)
  | 2 => (1857941/62500000 : ℚ)
  | 3 => (2426111/50000000 : ℚ)
  | 4 => (796762979/1000000000 : ℚ)
  | 5 => (1014588251/1000000000 : ℚ)
  | 6 => (45945423/1000000000 : ℚ)
  | 7 => (-15560333/125000000 : ℚ)
  | 8 => (5033313/40000000 : ℚ)
  | _ => 0
/-- Face masks: -1 on these (face code, flag-edge code) pairs, +1 otherwise. -/
def rep1MinusPairs : List (ℕ × ℕ) := [(536,520),(560,528),(608,544),(1030,1026),(1282,258),(1282,1280),(1408,1152),(1540,516),(1540,1028),(1600,576),(1600,1088),(1600,1536)]
def rep1MaskCode (fc ec : ℕ) : ℤ := if (fc, ec) ∈ rep1MinusPairs then -1 else 1
def rep1D : CanonicalCoeffQ (q1Faces 1 4) where
  faceCard := q1FaceCard 1 4
  mu := fun i => rep1MuN i.val
  faceMask := fun f s =>
    (rep1MaskCode (edgeCode f.val) (edgeCode (f.val.erase (canonicalLabel f.val (q1FaceCard 1 4 f) s))) : ℚ)
  switchMask := fun _ => -1
  sideFirst := fun e => rep1SideFirstCode (edgeCode e)
  sideSecond := fun e => rep1SideSecondCode (edgeCode e)
  leftFirst := fun i => rep1LeftFirstN i.val
  leftSecond := fun i => rep1LeftSecondN i.val
  rightFirst := fun i => rep1RightFirstN i.val
  rightSecond := fun i => rep1RightSecondN i.val
  width := (0 : ℚ)
def rep1Kap : Finset (Fin 11) → ℚ := fun e => rep1KapCode (edgeCode e)
def rep1Eta : ℚ := (1357679461/1000000000 : ℚ)

/-! ### q0m2: q0Faces 2 (historical start0) -/
def q0m2MuN : ℕ → ℚ
  | 0 => (40768173/500000000 : ℚ)
  | 1 => (-935783/31250000 : ℚ)
  | 2 => (40768173/500000000 : ℚ)
  | 3 => (523551/8000000 : ℚ)
  | 4 => (11560687/200000000 : ℚ)
  | 5 => (16444439/250000000 : ℚ)
  | 6 => (16444439/250000000 : ℚ)
  | 7 => (11560687/200000000 : ℚ)
  | 8 => (523551/8000000 : ℚ)
  | 9 => (-10358433/500000000 : ℚ)
  | 10 => (40776373/125000000 : ℚ)
  | _ => 0
def q0m2SideFirstCode : ℕ → ℚ
  | 3 => (1555963/5000000 : ℚ)
  | 6 => (1555963/5000000 : ℚ)
  | 12 => (20471393/500000000 : ℚ)
  | 24 => (284587637/1000000000 : ℚ)
  | 48 => (69654651/250000000 : ℚ)
  | 96 => (9972611/50000000 : ℚ)
  | 192 => (69654651/250000000 : ℚ)
  | 257 => (20471393/500000000 : ℚ)
  | 384 => (284587637/1000000000 : ℚ)
  | 513 => (-2033293/15625000 : ℚ)
  | 514 => (-13/1600000 : ℚ)
  | 516 => (-26001207/200000000 : ℚ)
  | 1025 => (-510491171/1000000000 : ℚ)
  | 1028 => (-509781653/1000000000 : ℚ)
  | 1032 => (16318851/50000000 : ℚ)
  | 1040 => (341065063/1000000000 : ℚ)
  | 1056 => (110487557/1000000000 : ℚ)
  | 1088 => (-4527929/40000000 : ℚ)
  | 1152 => (-341928027/1000000000 : ℚ)
  | 1280 => (-326517677/1000000000 : ℚ)
  | 1536 => (-2930609/1000000000 : ℚ)
  | _ => 0
def q0m2SideSecondCode : ℕ → ℚ
  | 3 => (-40785971/200000000 : ℚ)
  | 6 => (-40785971/200000000 : ℚ)
  | 12 => (3231407/25000000 : ℚ)
  | 24 => (-4675901/62500000 : ℚ)
  | 48 => (-68188893/1000000000 : ℚ)
  | 96 => (-4527713/1000000000 : ℚ)
  | 192 => (-68188893/1000000000 : ℚ)
  | 257 => (3231407/25000000 : ℚ)
  | 384 => (-4675901/62500000 : ℚ)
  | 513 => (-68861399/1000000000 : ℚ)
  | 514 => (31/6250000 : ℚ)
  | 516 => (-69002849/1000000000 : ℚ)
  | 1025 => (302170431/1000000000 : ℚ)
  | 1028 => (301418871/1000000000 : ℚ)
  | 1032 => (-71592229/500000000 : ℚ)
  | 1040 => (-24649311/125000000 : ℚ)
  | 1056 => (-14150343/250000000 : ℚ)
  | 1088 => (7256669/125000000 : ℚ)
  | 1152 => (98828369/500000000 : ℚ)
  | 1280 => (17907609/125000000 : ℚ)
  | 1536 => (2362171/1000000000 : ℚ)
  | _ => 0
def q0m2KapCode : ℕ → ℚ
  | 3 => (0 : ℚ)
  | 6 => (0 : ℚ)
  | 12 => (0 : ℚ)
  | 24 => (0 : ℚ)
  | 48 => (0 : ℚ)
  | 96 => (0 : ℚ)
  | 192 => (0 : ℚ)
  | 257 => (0 : ℚ)
  | 384 => (0 : ℚ)
  | 513 => (0 : ℚ)
  | 514 => (0 : ℚ)
  | 516 => (0 : ℚ)
  | 1025 => (0 : ℚ)
  | 1028 => (0 : ℚ)
  | 1032 => (0 : ℚ)
  | 1040 => (0 : ℚ)
  | 1056 => (0 : ℚ)
  | 1088 => (0 : ℚ)
  | 1152 => (0 : ℚ)
  | 1280 => (0 : ℚ)
  | 1536 => (0 : ℚ)
  | _ => 0
def q0m2LeftFirstN : ℕ → ℚ
  | 0 => (-209051769/1000000000 : ℚ)
  | 1 => (-251218191/500000000 : ℚ)
  | 2 => (-33802671/1000000000 : ℚ)
  | 3 => (681/625000 : ℚ)
  | 4 => (-8828747/250000000 : ℚ)
  | 5 => (-8828747/250000000 : ℚ)
  | 6 => (681/625000 : ℚ)
  | 7 => (-33802671/1000000000 : ℚ)
  | 8 => (-174281743/1000000000 : ℚ)
  | _ => 0
def q0m2LeftSecondN : ℕ → ℚ
  | 0 => (245913767/1000000000 : ℚ)
  | 1 => (2242193/6250000 : ℚ)
  | 2 => (119448559/1000000000 : ℚ)
  | 3 => (10163123/100000000 : ℚ)
  | 4 => (60110403/500000000 : ℚ)
  | 5 => (60110403/500000000 : ℚ)
  | 6 => (10163123/100000000 : ℚ)
  | 7 => (119448559/1000000000 : ℚ)
  | 8 => (225217787/1000000000 : ℚ)
  | _ => 0
def q0m2RightFirstN : ℕ → ℚ
  | 0 => (193450869/1000000000 : ℚ)
  | 1 => (-174281743/1000000000 : ℚ)
  | 2 => (-33802671/1000000000 : ℚ)
  | 3 => (681/625000 : ℚ)
  | 4 => (-8828747/250000000 : ℚ)
  | 5 => (-8828747/250000000 : ℚ)
  | 6 => (681/625000 : ℚ)
  | 7 => (-33802671/1000000000 : ℚ)
  | 8 => (-59271303/500000000 : ℚ)
  | _ => 0
def q0m2RightSecondN : ℕ → ℚ
  | 0 => (31274041/1000000000 : ℚ)
  | 1 => (225217787/1000000000 : ℚ)
  | 2 => (119448559/1000000000 : ℚ)
  | 3 => (10163123/100000000 : ℚ)
  | 4 => (60110403/500000000 : ℚ)
  | 5 => (60110403/500000000 : ℚ)
  | 6 => (10163123/100000000 : ℚ)
  | 7 => (119448559/1000000000 : ℚ)
  | 8 => (10170001/62500000 : ℚ)
  | _ => 0
/-- Face masks: -1 on these (face code, flag-edge code) pairs, +1 otherwise. -/
def q0m2MinusPairs : List (ℕ × ℕ) := [(518,514),(1048,1032),(1072,1040),(1120,1056),(1216,1088),(1281,1280),(1408,1152),(1537,513),(1537,1025),(1540,516),(1540,1028),(1540,1536)]
def q0m2MaskCode (fc ec : ℕ) : ℤ := if (fc, ec) ∈ q0m2MinusPairs then -1 else 1
def q0m2D : CanonicalCoeffQ (q0Faces 2) where
  faceCard := q0FaceCard 2
  mu := fun i => q0m2MuN i.val
  faceMask := fun f s =>
    (q0m2MaskCode (edgeCode f.val) (edgeCode (f.val.erase (canonicalLabel f.val (q0FaceCard 2 f) s))) : ℚ)
  switchMask := fun _ => -1
  sideFirst := fun e => q0m2SideFirstCode (edgeCode e)
  sideSecond := fun e => q0m2SideSecondCode (edgeCode e)
  leftFirst := fun i => q0m2LeftFirstN i.val
  leftSecond := fun i => q0m2LeftSecondN i.val
  rightFirst := fun i => q0m2RightFirstN i.val
  rightSecond := fun i => q0m2RightSecondN i.val
  width := (482812259/1000000000 : ℚ)
def q0m2Kap : Finset (Fin 11) → ℚ := fun e => q0m2KapCode (edgeCode e)
def q0m2Eta : ℚ := (0 : ℚ)

/-- Slot sums over `canonicalLabel` are sums over the face (orderIsoOfFin is a bijection). This avoids
evaluating `orderIsoOfFin` (which `decide` does not reduce; see A25 LEAD-STATUS C1810/C1812). -/
theorem sum_slots (f : Finset (Fin 11)) (h : f.card=3) (φ : Fin 11 → ℚ) :
    (∑ s : Fin 3, φ (canonicalLabel f h s)) = ∑ i ∈ f, φ i := by
  rw [← Finset.sum_coe_sort f]
  exact Equiv.sum_comp (f.orderIsoOfFin h).toEquiv (fun x : f => φ x.val)

/-- Decidable form of the balance condition for rep7, over ℤ (masks are ±1). -/
theorem rep7_balance_int : ∀ e ∈ faceEdges (q1Faces 7 4),
    (∑ f ∈ q1Faces 7 4, ∑ i ∈ f, (if f.erase i = e then rep7MaskCode (edgeCode f) (edgeCode (f.erase i)) else 0)) +
      (∑ j : Fin 9, if cycleEdge j = e then (-1 : ℤ) else 0) = 0 := by
  decide +kernel

theorem rep7_balance : CanonicalMaskBalancedQ rep7D := by
  intro e he
  have H := rep7_balance_int e he
  unfold canonicalEdgeSumQ switchSumQ
  have hslot : ∀ f : q1Faces 7 4, (∑ s : Fin 3, if rep7D.flagEdge f s = e then rep7D.faceMask f s else 0) =
      ∑ i ∈ f.val, (if f.val.erase i = e then (rep7MaskCode (edgeCode f.val) (edgeCode (f.val.erase i)) : ℚ) else 0) := by
    intro f
    exact sum_slots f.val (q1FaceCard 7 4 f)
      (fun i => if f.val.erase i = e then (rep7MaskCode (edgeCode f.val) (edgeCode (f.val.erase i)) : ℚ) else 0)
  have hsw : ∀ k : Fin 9, rep7D.switchMask k = -1 := fun _ => rfl
  simp only [hslot, hsw]
  rw [Finset.sum_coe_sort (q1Faces 7 4)
    (fun f => ∑ i ∈ f, (if f.erase i = e then (rep7MaskCode (edgeCode f) (edgeCode (f.erase i)) : ℚ) else 0))]
  have hc := congrArg (fun z : ℤ => (z : ℚ)) H
  push_cast [apply_ite] at hc
  simpa [apply_ite] using hc

theorem rep7_kap_nonneg : ∀ e ∈ faceEdges (q1Faces 7 4), 0 ≤ rep7Kap e := by
  intro e _
  unfold rep7Kap rep7KapCode
  split <;> norm_num

theorem rep7_eta_nonneg : 0 ≤ rep7Eta := by norm_num [rep7Eta]

/-- Decidable form of the balance condition for rep1, over ℤ (masks are ±1). -/
theorem rep1_balance_int : ∀ e ∈ faceEdges (q1Faces 1 4),
    (∑ f ∈ q1Faces 1 4, ∑ i ∈ f, (if f.erase i = e then rep1MaskCode (edgeCode f) (edgeCode (f.erase i)) else 0)) +
      (∑ j : Fin 9, if cycleEdge j = e then (-1 : ℤ) else 0) = 0 := by
  decide +kernel

theorem rep1_balance : CanonicalMaskBalancedQ rep1D := by
  intro e he
  have H := rep1_balance_int e he
  unfold canonicalEdgeSumQ switchSumQ
  have hslot : ∀ f : q1Faces 1 4, (∑ s : Fin 3, if rep1D.flagEdge f s = e then rep1D.faceMask f s else 0) =
      ∑ i ∈ f.val, (if f.val.erase i = e then (rep1MaskCode (edgeCode f.val) (edgeCode (f.val.erase i)) : ℚ) else 0) := by
    intro f
    exact sum_slots f.val (q1FaceCard 1 4 f)
      (fun i => if f.val.erase i = e then (rep1MaskCode (edgeCode f.val) (edgeCode (f.val.erase i)) : ℚ) else 0)
  have hsw : ∀ k : Fin 9, rep1D.switchMask k = -1 := fun _ => rfl
  simp only [hslot, hsw]
  rw [Finset.sum_coe_sort (q1Faces 1 4)
    (fun f => ∑ i ∈ f, (if f.erase i = e then (rep1MaskCode (edgeCode f) (edgeCode (f.erase i)) : ℚ) else 0))]
  have hc := congrArg (fun z : ℤ => (z : ℚ)) H
  push_cast [apply_ite] at hc
  simpa [apply_ite] using hc

theorem rep1_kap_nonneg : ∀ e ∈ faceEdges (q1Faces 1 4), 0 ≤ rep1Kap e := by
  intro e _
  unfold rep1Kap rep1KapCode
  split <;> norm_num

theorem rep1_eta_nonneg : 0 ≤ rep1Eta := by norm_num [rep1Eta]

/-- Decidable form of the balance condition for q0m2, over ℤ (masks are ±1). -/
theorem q0m2_balance_int : ∀ e ∈ faceEdges (q0Faces 2),
    (∑ f ∈ q0Faces 2, ∑ i ∈ f, (if f.erase i = e then q0m2MaskCode (edgeCode f) (edgeCode (f.erase i)) else 0)) +
      (∑ j : Fin 9, if cycleEdge j = e then (-1 : ℤ) else 0) = 0 := by
  decide +kernel

theorem q0m2_balance : CanonicalMaskBalancedQ q0m2D := by
  intro e he
  have H := q0m2_balance_int e he
  unfold canonicalEdgeSumQ switchSumQ
  have hslot : ∀ f : q0Faces 2, (∑ s : Fin 3, if q0m2D.flagEdge f s = e then q0m2D.faceMask f s else 0) =
      ∑ i ∈ f.val, (if f.val.erase i = e then (q0m2MaskCode (edgeCode f.val) (edgeCode (f.val.erase i)) : ℚ) else 0) := by
    intro f
    exact sum_slots f.val (q0FaceCard 2 f)
      (fun i => if f.val.erase i = e then (q0m2MaskCode (edgeCode f.val) (edgeCode (f.val.erase i)) : ℚ) else 0)
  have hsw : ∀ k : Fin 9, q0m2D.switchMask k = -1 := fun _ => rfl
  simp only [hslot, hsw]
  rw [Finset.sum_coe_sort (q0Faces 2)
    (fun f => ∑ i ∈ f, (if f.erase i = e then (q0m2MaskCode (edgeCode f) (edgeCode (f.erase i)) : ℚ) else 0))]
  have hc := congrArg (fun z : ℤ => (z : ℚ)) H
  push_cast [apply_ite] at hc
  simpa [apply_ite] using hc

theorem q0m2_kap_nonneg : ∀ e ∈ faceEdges (q0Faces 2), 0 ≤ q0m2Kap e := by
  intro e _
  unfold q0m2Kap q0m2KapCode
  split <;> norm_num

theorem q0m2_eta_nonneg : 0 ≤ q0m2Eta := by norm_num [q0m2Eta]

end N11Formalization.Class33RepData
#print axioms N11Formalization.Class33RepData.rep7_balance
#print axioms N11Formalization.Class33RepData.rep7_kap_nonneg
#print axioms N11Formalization.Class33RepData.rep1_balance
#print axioms N11Formalization.Class33RepData.rep1_kap_nonneg
#print axioms N11Formalization.Class33RepData.q0m2_balance
#print axioms N11Formalization.Class33RepData.q0m2_kap_nonneg
