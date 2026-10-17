import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((6137230643:ℚ)/10000000000),((3337321627:ℚ)/5000000000),((3382678373:ℚ)/53400000000),((22:ℚ)/155),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((394277113:ℚ)/625000000),((64405632983915020234003715681:ℚ)/442452208125000000000000000000),((-117402562274805321:ℚ)/486400000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((3308369121:ℚ)/5000000000),((6913973059:ℚ)/10000000000),((932289563:ℚ)/15800000000),((176:ℚ)/1335),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5143281147:ℚ)/10000000000),((104619560781949292751525758023254639244513:ℚ)/742451320518750000000000000000000000000000),((-64001217971438387:ℚ)/243200000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((85703209:ℚ)/125000000),((7033591093:ℚ)/10000000000),((6406408907:ℚ)/112500000000),((352:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((892188753:ℚ)/2000000000),((738583246008994762629273603419322763921783:ℚ)/5308354467773437500000000000000000000000000),((-1666214635242123:ℚ)/6080000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((6975964201:ℚ)/10000000000),((1788294997:ℚ)/2500000000),((142882273:ℚ)/2600000000),((704:ℚ)/5625),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4080659779:ℚ)/10000000000),((42776399167750782806609483837184257863:ℚ)/308496093750000000000000000000000000000),((-135943394108363147:ℚ)/486400000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((443477469:ℚ)/625000000),((727274119:ℚ)/1000000000),((616725881:ℚ)/11630000000),((8:ℚ)/65),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1831809347:ℚ)/5000000000),((3209364827129222188344220195323281737:ℚ)/23215578851562500000000000000000000000),((-8661806629914343:ℚ)/30400000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((721528423:ℚ)/1000000000),((1478455211:ℚ)/2000000000),((1209544789:ℚ)/23640000000),((704:ℚ)/5815),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((25563331:ℚ)/80000000),((3156374965811050849708163338642942950225317:ℚ)/22893008221246125000000000000000000000000000),((-14123374212146981:ℚ)/48640000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((3667449939:ℚ)/5000000000),((7631271753:ℚ)/10000000000),((5808728247:ℚ)/122000000000),((352:ℚ)/2955),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2649010773:ℚ)/10000000000),((66283962597626833071436807546525581994786121:ℚ)/480067305744375000000000000000000000000000000),((-3786261457194707:ℚ)/12800000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((7574049443:ℚ)/10000000000),((1013624721:ℚ)/1250000000),((222125093:ℚ)/5400000000),((176:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((826618649:ℚ)/10000000000),((2651606832491555205143952192836420869:ℚ)/19151521875000000000000000000000000000),((-149164515152448921:ℚ)/486400000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((2013013909:ℚ)/2500000000),((1252161981:ℚ)/1250000000),((427838019:ℚ)/20000000000),((44:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1176875134610305171039594478327459780527:ℚ)/8303765625000000000000000000000000000000),((-19702391:ℚ)/64000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((1245150593:ℚ)/1250000000),((276540647:ℚ)/200000000),((-7740647:ℚ)/3200000000),((11:ℚ)/125),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2524844624538737:ℚ)/16000000000000000),((-19702391:ℚ)/64000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC16
#check @N11Formalization.C450Source23GroupedC16.bound
#print axioms N11Formalization.C450Source23GroupedC16.valid0
#print axioms N11Formalization.C450Source23GroupedC16.valid1
#print axioms N11Formalization.C450Source23GroupedC16.valid2
#print axioms N11Formalization.C450Source23GroupedC16.valid3
#print axioms N11Formalization.C450Source23GroupedC16.valid4
#print axioms N11Formalization.C450Source23GroupedC16.valid5
#print axioms N11Formalization.C450Source23GroupedC16.valid6
#print axioms N11Formalization.C450Source23GroupedC16.valid7
#print axioms N11Formalization.C450Source23GroupedC16.valid8
#print axioms N11Formalization.C450Source23GroupedC16.valid9
#print axioms N11Formalization.C450Source23GroupedC16.bound
#print axioms N11Formalization.C450Source23GroupedC16.endpoint_checks
