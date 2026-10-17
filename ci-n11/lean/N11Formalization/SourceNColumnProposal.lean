import N11Formalization.SourceB41Proposal

/-! Rational PROPOSED dependent N columns and finite residual bounds.
Candidates are not substituted for exact N. Numeric statements here refer
only to integer tables; actual-real semantics is a separate consumer. -/
set_option autoImplicit false
namespace N11Formalization.SourceNColumnProposal
open N11Formalization SourceB41Proposal
section
-- Only evaluator stack depth; default heartbeats and kernel remain unchanged.
set_option maxRecDepth 10000

def YN : Fin 41 → Fin 4 → ℤ :=
 ![![42809939,-33496473,-172,25756839],
   ![-46003650,4655677,27691318,13079200],
   ![-88312959,8937478,53158875,25108070],
   ![46866935,-36670854,-188,28197753],
   ![37805363,-29580661,-152,22745807],
   ![52089722,0,0,0],
   ![2588161,-4438413,11774367,-856496],
   ![-63636544,-42320472,-32337911,-52156139],
   ![-52092790,40759804,209,14507149],
   ![21573661,-23869533,-31435166,-33431246],
   ![37806826,8097498,-22757385,22746687],
   ![-33388328,26124570,20097721,-20088274],
   ![2089843,-3583853,9507361,-691589],
   ![2090000,-3584122,9508074,-691641],
   ![-32064327,-21323871,-16293992,-26279735],
   ![-42810470,33496888,172,11922147],
   ![-41389175,32384802,24913740,-24902028],
   ![-46309969,-30797708,-23533139,-37955379],
   ![46004017,9853180,-27691591,27678573],
   ![31158680,-34474590,-45401579,-48284502],
   ![-59827638,6054697,36012494,17009469],
   ![67743131,0,0,0],
   ![-37807975,29582705,22758077,-22747379],
   ![-29531141,-19639216,-15006714,-24203550],
   ![19869272,-21983762,-28951686,-30790069],
   ![2538465,-4353191,11548286,-840051],
   ![2538273,-4352862,11547412,-839987],
   ![-68355415,53484433,275,19036074],
   ![33389477,79737897,-20098413,20088965],
   ![-27446519,-25867970,-8988772,-26176838],
   ![-10221146,4399929,-3347819,29673919],
   ![-37808496,29583113,152,83115674],
   ![20520990,-25719678,-22529699,-34997033],
   ![-36618202,-24352353,-18608115,-30012064],
   ![24637620,-27259558,-35899686,-38179255],
   ![41388656,-32384395,88318967,24901715],
   ![7641196,29846136,-8390200,998476],
   ![3644599,-6250090,16580440,-1206102],
   ![3644885,-6250581,16581743,-1206197],
   ![60367515,12929566,-36337533,36320452],
   ![42817520,-47374166,-62389774,-66351419]]

def BFL : Fin 41 → Fin 4 → ℤ :=
 ![![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![3303,0,0,0],
   ![-37857,0,0,0],
   ![0,0,0,21118],
   ![0,0,0,31585],
   ![0,0,-3309,0],
   ![0,0,37852,0],
   ![0,21118,0,0],
   ![0,-31591,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![-3309,0,0,0],
   ![37851,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![100000,100000,100000,100000]]

def BFH : Fin 41 → Fin 4 → ℤ :=
 ![![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![3309,0,0,0],
   ![-37851,0,0,0],
   ![0,0,0,21124],
   ![0,0,0,31591],
   ![0,0,-3303,0],
   ![0,0,37858,0],
   ![0,21124,0,0],
   ![0,-31585,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![-3303,0,0,0],
   ![37857,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![0,0,0,0],
   ![100000,100000,100000,100000]]


def FreeBinding (i : Fin 41) (a : Fin 4) : Prop :=
  BFL i a = loEntry i (freeCol a) ∧ BFH i a = hiEntry i (freeCol a)
instance freeBindingDecidable (i : Fin 41) (a : Fin 4) :
    Decidable (FreeBinding i a) := by unfold FreeBinding; infer_instance

private theorem free0 (a : Fin 4) : FreeBinding 0 a := by
  fin_cases a <;> decide
private theorem free1 (a : Fin 4) : FreeBinding 1 a := by
  fin_cases a <;> decide
private theorem free2 (a : Fin 4) : FreeBinding 2 a := by
  fin_cases a <;> decide
private theorem free3 (a : Fin 4) : FreeBinding 3 a := by
  fin_cases a <;> decide
private theorem free4 (a : Fin 4) : FreeBinding 4 a := by
  fin_cases a <;> decide
private theorem free5 (a : Fin 4) : FreeBinding 5 a := by
  fin_cases a <;> decide
private theorem free6 (a : Fin 4) : FreeBinding 6 a := by
  fin_cases a <;> decide
private theorem free7 (a : Fin 4) : FreeBinding 7 a := by
  fin_cases a <;> decide
private theorem free8 (a : Fin 4) : FreeBinding 8 a := by
  fin_cases a <;> decide
private theorem free9 (a : Fin 4) : FreeBinding 9 a := by
  fin_cases a <;> decide
private theorem free10 (a : Fin 4) : FreeBinding 10 a := by
  fin_cases a <;> decide
private theorem free11 (a : Fin 4) : FreeBinding 11 a := by
  fin_cases a <;> decide
private theorem free12 (a : Fin 4) : FreeBinding 12 a := by
  fin_cases a <;> decide
private theorem free13 (a : Fin 4) : FreeBinding 13 a := by
  fin_cases a <;> decide
private theorem free14 (a : Fin 4) : FreeBinding 14 a := by
  fin_cases a <;> decide
private theorem free15 (a : Fin 4) : FreeBinding 15 a := by
  fin_cases a <;> decide
private theorem free16 (a : Fin 4) : FreeBinding 16 a := by
  fin_cases a <;> decide
private theorem free17 (a : Fin 4) : FreeBinding 17 a := by
  fin_cases a <;> decide
private theorem free18 (a : Fin 4) : FreeBinding 18 a := by
  fin_cases a <;> decide
private theorem free19 (a : Fin 4) : FreeBinding 19 a := by
  fin_cases a <;> decide
private theorem free20 (a : Fin 4) : FreeBinding 20 a := by
  fin_cases a <;> decide
private theorem free21 (a : Fin 4) : FreeBinding 21 a := by
  fin_cases a <;> decide
private theorem free22 (a : Fin 4) : FreeBinding 22 a := by
  fin_cases a <;> decide
private theorem free23 (a : Fin 4) : FreeBinding 23 a := by
  fin_cases a <;> decide
private theorem free24 (a : Fin 4) : FreeBinding 24 a := by
  fin_cases a <;> decide
private theorem free25 (a : Fin 4) : FreeBinding 25 a := by
  fin_cases a <;> decide
private theorem free26 (a : Fin 4) : FreeBinding 26 a := by
  fin_cases a <;> decide
private theorem free27 (a : Fin 4) : FreeBinding 27 a := by
  fin_cases a <;> decide
private theorem free28 (a : Fin 4) : FreeBinding 28 a := by
  fin_cases a <;> decide
private theorem free29 (a : Fin 4) : FreeBinding 29 a := by
  fin_cases a <;> decide
private theorem free30 (a : Fin 4) : FreeBinding 30 a := by
  fin_cases a <;> decide
private theorem free31 (a : Fin 4) : FreeBinding 31 a := by
  fin_cases a <;> decide
private theorem free32 (a : Fin 4) : FreeBinding 32 a := by
  fin_cases a <;> decide
private theorem free33 (a : Fin 4) : FreeBinding 33 a := by
  fin_cases a <;> decide
private theorem free34 (a : Fin 4) : FreeBinding 34 a := by
  fin_cases a <;> decide
private theorem free35 (a : Fin 4) : FreeBinding 35 a := by
  fin_cases a <;> decide
private theorem free36 (a : Fin 4) : FreeBinding 36 a := by
  fin_cases a <;> decide
private theorem free37 (a : Fin 4) : FreeBinding 37 a := by
  fin_cases a <;> decide
private theorem free38 (a : Fin 4) : FreeBinding 38 a := by
  fin_cases a <;> decide
private theorem free39 (a : Fin 4) : FreeBinding 39 a := by
  fin_cases a <;> decide
private theorem free40 (a : Fin 4) : FreeBinding 40 a := by
  fin_cases a <;> decide

theorem free_binding (i : Fin 41) (a : Fin 4) : FreeBinding i a := by
  fin_cases i
  · exact free0 a
  · exact free1 a
  · exact free2 a
  · exact free3 a
  · exact free4 a
  · exact free5 a
  · exact free6 a
  · exact free7 a
  · exact free8 a
  · exact free9 a
  · exact free10 a
  · exact free11 a
  · exact free12 a
  · exact free13 a
  · exact free14 a
  · exact free15 a
  · exact free16 a
  · exact free17 a
  · exact free18 a
  · exact free19 a
  · exact free20 a
  · exact free21 a
  · exact free22 a
  · exact free23 a
  · exact free24 a
  · exact free25 a
  · exact free26 a
  · exact free27 a
  · exact free28 a
  · exact free29 a
  · exact free30 a
  · exact free31 a
  · exact free32 a
  · exact free33 a
  · exact free34 a
  · exact free35 a
  · exact free36 a
  · exact free37 a
  · exact free38 a
  · exact free39 a
  · exact free40 a

def CBL (i : Fin 41) (a : Fin 4) : ℤ :=
  ∑ k : Fin 41, CN i k * (if 0 ≤ CN i k then -BFH k a else -BFL k a)
def CBH (i : Fin 41) (a : Fin 4) : ℤ :=
  ∑ k : Fin 41, CN i k * (if 0 ≤ CN i k then -BFL k a else -BFH k a)
def defectN (i : Fin 41) (a : Fin 4) : ℤ :=
  max |CBL i a - YN i a * 100000| |CBH i a - YN i a * 100000|
def errorN (i : Fin 41) (a : Fin 4) : ℤ :=
  defectN i a * 100000000 + ∑ k : Fin 41, magN i k * |YN k a|
def ErrorOK (i : Fin 41) (a : Fin 4) : Prop :=
  errorN i a ≤ 4000000000000000000
instance errorDecidable (i : Fin 41) (a : Fin 4) : Decidable (ErrorOK i a) := by
  unfold ErrorOK
  infer_instance

private theorem err0 (a : Fin 4) : ErrorOK 0 a := by
  fin_cases a <;> decide
private theorem err1 (a : Fin 4) : ErrorOK 1 a := by
  fin_cases a <;> decide
private theorem err2 (a : Fin 4) : ErrorOK 2 a := by
  fin_cases a <;> decide
private theorem err3 (a : Fin 4) : ErrorOK 3 a := by
  fin_cases a <;> decide
private theorem err4 (a : Fin 4) : ErrorOK 4 a := by
  fin_cases a <;> decide
private theorem err5 (a : Fin 4) : ErrorOK 5 a := by
  fin_cases a <;> decide
private theorem err6 (a : Fin 4) : ErrorOK 6 a := by
  fin_cases a <;> decide
private theorem err7 (a : Fin 4) : ErrorOK 7 a := by
  fin_cases a <;> decide
private theorem err8 (a : Fin 4) : ErrorOK 8 a := by
  fin_cases a <;> decide
private theorem err9 (a : Fin 4) : ErrorOK 9 a := by
  fin_cases a <;> decide
private theorem err10 (a : Fin 4) : ErrorOK 10 a := by
  fin_cases a <;> decide
private theorem err11 (a : Fin 4) : ErrorOK 11 a := by
  fin_cases a <;> decide
private theorem err12 (a : Fin 4) : ErrorOK 12 a := by
  fin_cases a <;> decide
private theorem err13 (a : Fin 4) : ErrorOK 13 a := by
  fin_cases a <;> decide
private theorem err14 (a : Fin 4) : ErrorOK 14 a := by
  fin_cases a <;> decide
private theorem err15 (a : Fin 4) : ErrorOK 15 a := by
  fin_cases a <;> decide
private theorem err16 (a : Fin 4) : ErrorOK 16 a := by
  fin_cases a <;> decide
private theorem err17 (a : Fin 4) : ErrorOK 17 a := by
  fin_cases a <;> decide
private theorem err18 (a : Fin 4) : ErrorOK 18 a := by
  fin_cases a <;> decide
private theorem err19 (a : Fin 4) : ErrorOK 19 a := by
  fin_cases a <;> decide
private theorem err20 (a : Fin 4) : ErrorOK 20 a := by
  fin_cases a <;> decide
private theorem err21 (a : Fin 4) : ErrorOK 21 a := by
  fin_cases a <;> decide
private theorem err22 (a : Fin 4) : ErrorOK 22 a := by
  fin_cases a <;> decide
private theorem err23 (a : Fin 4) : ErrorOK 23 a := by
  fin_cases a <;> decide
private theorem err24 (a : Fin 4) : ErrorOK 24 a := by
  fin_cases a <;> decide
private theorem err25 (a : Fin 4) : ErrorOK 25 a := by
  fin_cases a <;> decide
private theorem err26 (a : Fin 4) : ErrorOK 26 a := by
  fin_cases a <;> decide
private theorem err27 (a : Fin 4) : ErrorOK 27 a := by
  fin_cases a <;> decide
private theorem err28 (a : Fin 4) : ErrorOK 28 a := by
  fin_cases a <;> decide
private theorem err29 (a : Fin 4) : ErrorOK 29 a := by
  fin_cases a <;> decide
private theorem err30 (a : Fin 4) : ErrorOK 30 a := by
  fin_cases a <;> decide
private theorem err31 (a : Fin 4) : ErrorOK 31 a := by
  fin_cases a <;> decide
private theorem err32 (a : Fin 4) : ErrorOK 32 a := by
  fin_cases a <;> decide
private theorem err33 (a : Fin 4) : ErrorOK 33 a := by
  fin_cases a <;> decide
private theorem err34 (a : Fin 4) : ErrorOK 34 a := by
  fin_cases a <;> decide
private theorem err35 (a : Fin 4) : ErrorOK 35 a := by
  fin_cases a <;> decide
private theorem err36 (a : Fin 4) : ErrorOK 36 a := by
  fin_cases a <;> decide
private theorem err37 (a : Fin 4) : ErrorOK 37 a := by
  fin_cases a <;> decide
private theorem err38 (a : Fin 4) : ErrorOK 38 a := by
  fin_cases a <;> decide
private theorem err39 (a : Fin 4) : ErrorOK 39 a := by
  fin_cases a <;> decide
private theorem err40 (a : Fin 4) : ErrorOK 40 a := by
  fin_cases a <;> decide

theorem all_errors (i : Fin 41) (a : Fin 4) : ErrorOK i a := by
  fin_cases i
  · exact err0 a
  · exact err1 a
  · exact err2 a
  · exact err3 a
  · exact err4 a
  · exact err5 a
  · exact err6 a
  · exact err7 a
  · exact err8 a
  · exact err9 a
  · exact err10 a
  · exact err11 a
  · exact err12 a
  · exact err13 a
  · exact err14 a
  · exact err15 a
  · exact err16 a
  · exact err17 a
  · exact err18 a
  · exact err19 a
  · exact err20 a
  · exact err21 a
  · exact err22 a
  · exact err23 a
  · exact err24 a
  · exact err25 a
  · exact err26 a
  · exact err27 a
  · exact err28 a
  · exact err29 a
  · exact err30 a
  · exact err31 a
  · exact err32 a
  · exact err33 a
  · exact err34 a
  · exact err35 a
  · exact err36 a
  · exact err37 a
  · exact err38 a
  · exact err39 a
  · exact err40 a

end
end N11Formalization.SourceNColumnProposal
#check @N11Formalization.SourceNColumnProposal.free_binding
#check @N11Formalization.SourceNColumnProposal.all_errors
#print axioms N11Formalization.SourceNColumnProposal.all_errors
