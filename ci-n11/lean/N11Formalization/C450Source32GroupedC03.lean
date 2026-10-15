import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7135407857:ℚ)/10000000000),((7375169043:ℚ)/10000000000),((-42026183301:ℚ)/49600000000),((-72920302141:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1757323619:ℚ)/5000000000),((693369295173835072791232564612345885949701:ℚ)/1601714713050000000000000000000000000000000),((2404424408097891405209571721:ℚ)/2772480000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((725490657:ℚ)/1000000000),((3747224297:ℚ)/5000000000),((-21430570079:ℚ)/25275000000),((-7447378541:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((605011643:ℚ)/2000000000),((12426232297665592437503046187697504591772286238664177369:ℚ)/28769453046875000000000000000000000000000000000000000000),((201054677574346574038419387:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7374377409:ℚ)/10000000000),((3806854419:ℚ)/5000000000),((-21847980933:ℚ)/25750000000),((-76026906317:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((3053443:ℚ)/12500000),((250233282805490907887449260110243445955396045171060960207:ℚ)/580542123276367187500000000000000000000000000000000000000),((11172441:ℚ)/12800000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((1498764381:ℚ)/2000000000),((1546590163:ℚ)/2000000000),((-8906131141:ℚ)/10490000000),((-15515936953:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((66941059:ℚ)/400000000),((610844868892204425619797689070017289068639566467866516501:ℚ)/1419863963520000000000000000000000000000000000000000000000),((11172441:ℚ)/12800000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((3806620741:ℚ)/5000000000),((513109649:ℚ)/625000000),((-2991767543:ℚ)/3337500000),((-39566069633:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((28616909749956064638022171410049570958159299781021224230023:ℚ)/62461061520000000000000000000000000000000000000000000000000),((11172441:ℚ)/12800000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((8090695677:ℚ)/10000000000),((9162724001:ℚ)/10000000000),((-54539068007:ℚ)/57200000000),((-85339043801:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((142099843603153912888074724516137072852063236885698509394793:ℚ)/291824881920000000000000000000000000000000000000000000000000),((11172441:ℚ)/12800000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((9044735123:ℚ)/10000000000),((11066964989:ℚ)/10000000000),(-1:ℚ),((-97741556599:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((489751886644162851233731451978222667510513262702467053441:ℚ)/960000000000000000000000000000000000000000000000000000000),((11172441:ℚ)/12800000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((5475250619:ℚ)/5000000000),((7435968377:ℚ)/5000000000),(-1:ℚ),((-20419419349:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1309165571201305211687186354098168051:ℚ)/2491801600000000000000000000000000000),((11172441:ℚ)/12800000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
private theorem node0_2 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_4 node4_8
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_8
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7]
theorem packet_count : packets.length = 8 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC03
#check @N11Formalization.C450Source32GroupedC03.bound
#print axioms N11Formalization.C450Source32GroupedC03.valid0
#print axioms N11Formalization.C450Source32GroupedC03.valid1
#print axioms N11Formalization.C450Source32GroupedC03.valid2
#print axioms N11Formalization.C450Source32GroupedC03.valid3
#print axioms N11Formalization.C450Source32GroupedC03.valid4
#print axioms N11Formalization.C450Source32GroupedC03.valid5
#print axioms N11Formalization.C450Source32GroupedC03.valid6
#print axioms N11Formalization.C450Source32GroupedC03.valid7
#print axioms N11Formalization.C450Source32GroupedC03.bound
#print axioms N11Formalization.C450Source32GroupedC03.endpoint_checks
