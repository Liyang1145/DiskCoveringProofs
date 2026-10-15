import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/8),((7:ℚ)/16),((5507818909:ℚ)/10000000000),((730899471:ℚ)/1250000000),((26763456727:ℚ)/51500000000),((7756296297:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3800892591:ℚ)/5000000000),((-411189620418470800832316012133922888724795719398608254023:ℚ)/1227389200000000000000000000000000000000000000000000000000),((-271798717842557256388976413:ℚ)/693120000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((1149925027:ℚ)/2000000000),((6088685183:ℚ)/10000000000),((5497775081:ℚ)/10680000000),((63740796281:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((891007929:ℚ)/1250000000),((-151056627231515125238446927842024341767940509020387238723819:ℚ)/455872045312500000000000000000000000000000000000000000000000),((-5764978499622060068651849759:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((2995558573:ℚ)/5000000000),((388082673:ℚ)/625000000),((14106675719:ℚ)/27175000000),((1345526237:ℚ)/2225000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((662747217:ℚ)/1000000000),((-25053475017534917118448857904477888938933792991714472747:ℚ)/74834111621093750000000000000000000000000000000000000000),((-67875042268034326479881197:ℚ)/173280000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6111755959:ℚ)/10000000000),((6329893999:ℚ)/10000000000),((28575267877:ℚ)/55300000000),((65429257993:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6365043899:ℚ)/10000000000),((-9898989402178826315746505089860538161493864262642298332717:ℚ)/29726037520605468750000000000000000000000000000000000000000),((-5772147974409514317485426431:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((6232328373:ℚ)/10000000000),((322520117:ℚ)/500000000),((28936985119:ℚ)/56250000000),((3313640819:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1218619631:ℚ)/2000000000),((-12311248572859672309497361116627307402775057556423947:ℚ)/37158481274414062500000000000000000000000000000000000),((-756716321490831546799261:ℚ)/1945600000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((1270567571:ℚ)/2000000000),((1314170203:ℚ)/2000000000),((5859702713:ℚ)/11440000000),((13423191421:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((726283:ℚ)/1250000),((-3356604337807119266614590904502150478425687837115501305971:ℚ)/10180371093750000000000000000000000000000000000000000000000),((-229147730310723119304667079:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6473287631:ℚ)/10000000000),((669124303:ℚ)/1000000000),((29659862893:ℚ)/58150000000),((6795870121:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1102966257:ℚ)/2000000000),((-324693363266667147235441322088207361322677182979165098929:ℚ)/989338979200000000000000000000000000000000000000000000000),((-57050969616599711876319679:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((659368071:ℚ)/1000000000),((851447649:ℚ)/1250000000),((3002104213:ℚ)/5910000000),((8600133543:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((208184769:ℚ)/400000000),((-927029094805492468249644780133365747110846984834408532569:ℚ)/2837113368154907226562500000000000000000000000000000000000),((-266262019130970565603532893:ℚ)/693120000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((6714019901:ℚ)/10000000000),((3526053141:ℚ)/5000000000),((30382059703:ℚ)/61000000000),((11747457329:ℚ)/19700000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((487677149:ℚ)/1000000000),((-14199601310721328849984006660879396184564046378622358747:ℚ)/44387793750000000000000000000000000000000000000000000000),((-4186052478029500582806606133:ℚ)/11089920000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((6954546947:ℚ)/10000000000),((470788441:ℚ)/625000000),((31103640841:ℚ)/64800000000),((4615519087:ℚ)/7625000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((4151099937:ℚ)/10000000000),((-69078806813749863614867033142631674122938178917784426591:ℚ)/224431896972656250000000000000000000000000000000000000000),((-1103817891887501610135069:ℚ)/3040000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((92938241:ℚ)/125000000),((4724675217:ℚ)/5000000000),((406814723:ℚ)/1000000000),((14544242173:ℚ)/21600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2087184001:ℚ)/10000000000),((-48670655276298197060448718918684573704807923000719859447:ℚ)/188956800000000000000000000000000000000000000000000000000),((-4528266479302063:ℚ)/12160000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((584487839:ℚ)/625000000),((13268890867:ℚ)/10000000000),((2393463517:ℚ)/6900000000),((114002236069:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-32210579286886332865584572255359246101715349823586193219499:ℚ)/147200000000000000000000000000000000000000000000000000000000),((-385643029:ℚ)/1024000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC23
#check @N11Formalization.C450Source34GroupedC23.bound
#print axioms N11Formalization.C450Source34GroupedC23.valid0
#print axioms N11Formalization.C450Source34GroupedC23.valid1
#print axioms N11Formalization.C450Source34GroupedC23.valid2
#print axioms N11Formalization.C450Source34GroupedC23.valid3
#print axioms N11Formalization.C450Source34GroupedC23.valid4
#print axioms N11Formalization.C450Source34GroupedC23.valid5
#print axioms N11Formalization.C450Source34GroupedC23.valid6
#print axioms N11Formalization.C450Source34GroupedC23.valid7
#print axioms N11Formalization.C450Source34GroupedC23.valid8
#print axioms N11Formalization.C450Source34GroupedC23.valid9
#print axioms N11Formalization.C450Source34GroupedC23.valid10
#print axioms N11Formalization.C450Source34GroupedC23.valid11
#print axioms N11Formalization.C450Source34GroupedC23.bound
#print axioms N11Formalization.C450Source34GroupedC23.endpoint_checks
