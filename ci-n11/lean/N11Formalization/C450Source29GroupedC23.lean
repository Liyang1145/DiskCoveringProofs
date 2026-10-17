import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/8),((7:ℚ)/16),((5627654777:ℚ)/10000000000),((372135567:ℚ)/625000000),((25522964331:ℚ)/51500000000),((3724948969:ℚ)/6200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3685053601:ℚ)/5000000000),((-9783568523436523571325603552133114797601887781192728244063:ℚ)/47407907850000000000000000000000000000000000000000000000000),((-66047201600151558554352053:ℚ)/173280000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((46945851:ℚ)/80000000),((6194488619:ℚ)/10000000000),((69985851:ℚ)/142400000),((61281420333:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1721502769:ℚ)/2500000000),((-2758014509964079965972238402435735459195917100593582296644817:ℚ)/13524204010937500000000000000000000000000000000000000000000000),((-5629055044383623925566337999:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6108585073:ℚ)/10000000000),((789321651:ℚ)/1250000000),((26965755219:ℚ)/54350000000),((7765251557:ℚ)/13350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3186029961:ℚ)/5000000000),((-1211532195504027846961056636027779482695327478476765161352619:ℚ)/5856816911913281250000000000000000000000000000000000000000000),((-265976517026101923729013277:ℚ)/693120000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6228685811:ℚ)/10000000000),((3217305597:ℚ)/5000000000),((27326057433:ℚ)/55300000000),((31481139179:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((305073391:ℚ)/500000000),((-2958087642473698904934631482534124664542518867523407428845397:ℚ)/14383686405282971191406250000000000000000000000000000000000000),((-4251001371943767147403872893:ℚ)/11089920000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((6348739373:ℚ)/10000000000),((6554604989:ℚ)/10000000000),((9228739373:ℚ)/18750000000),((9114604989:ℚ)/15800000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5820081611:ℚ)/10000000000),((-177235053763958353584457126581604525371750626971425721:ℚ)/866670117187500000000000000000000000000000000000000000),((-5660778748360359165805232639:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((6468748201:ℚ)/10000000000),((6674556839:ℚ)/10000000000),((2157403431:ℚ)/4400000000),((7182433097:ℚ)/12500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2763110269:ℚ)/5000000000),((-300420677223312228117369854163029976040101252417948709293:ℚ)/1477050781250000000000000000000000000000000000000000000000),((-5652497541496602190496058839:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((658871457:ℚ)/1000000000),((6794468841:ℚ)/10000000000),((2840614371:ℚ)/5815000000),((65481281887:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5217744449:ℚ)/10000000000),((-232797247755401827858561469197800419103407254357635187772608833:ℚ)/1150601232809600000000000000000000000000000000000000000000000000),((-16929477663988008397307027237:ℚ)/44359680000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6708640603:ℚ)/10000000000),((1382868591:ℚ)/2000000000),((9588640603:ℚ)/19700000000),((13264080137:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1222963867:ℚ)/2500000000),((-153613659453730424781107287842820561876863401834251261276277:ℚ)/763100274041537500000000000000000000000000000000000000000000),((-675931767881918001080261237:ℚ)/1774387200000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((3414264141:ℚ)/5000000000),((7153984723:ℚ)/10000000000),((14562792423:ℚ)/30500000000),((67997893061:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2272387059:ℚ)/5000000000),((-22572538153141163903529835151520351246706617473224893867250283:ℚ)/115216153378650000000000000000000000000000000000000000000000000),((-5558743624086306121813476511:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((176704897:ℚ)/250000000),((1908221713:ℚ)/2500000000),((248704897:ℚ)/540000000),((17837551991:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((235195847:ℚ)/625000000),((-24079962824227242552487188543660333962976247033261126974859:ℚ)/129272772656250000000000000000000000000000000000000000000000),((-139201986908521:ℚ)/380000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((7547145013:ℚ)/10000000000),((381790201:ℚ)/400000000),((31281435039:ℚ)/80000000000),((3389331407:ℚ)/5184000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((295014399:ℚ)/2500000000),((-384720553963782690013314413974580535947078488845423449:ℚ)/2612138803200000000000000000000000000000000000000000000),((-23095007394270061:ℚ)/60800000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((9459155741:ℚ)/10000000000),((1669829269:ℚ)/1250000000),((12339155741:ℚ)/36800000000),((13928804883:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-751752896375864327983845103862115651910271896475410972503:ℚ)/6612500000000000000000000000000000000000000000000000000000),((-390497621:ℚ)/1024000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC23
#check @N11Formalization.C450Source29GroupedC23.bound
#print axioms N11Formalization.C450Source29GroupedC23.valid0
#print axioms N11Formalization.C450Source29GroupedC23.valid1
#print axioms N11Formalization.C450Source29GroupedC23.valid2
#print axioms N11Formalization.C450Source29GroupedC23.valid3
#print axioms N11Formalization.C450Source29GroupedC23.valid4
#print axioms N11Formalization.C450Source29GroupedC23.valid5
#print axioms N11Formalization.C450Source29GroupedC23.valid6
#print axioms N11Formalization.C450Source29GroupedC23.valid7
#print axioms N11Formalization.C450Source29GroupedC23.valid8
#print axioms N11Formalization.C450Source29GroupedC23.valid9
#print axioms N11Formalization.C450Source29GroupedC23.valid10
#print axioms N11Formalization.C450Source29GroupedC23.valid11
#print axioms N11Formalization.C450Source29GroupedC23.bound
#print axioms N11Formalization.C450Source29GroupedC23.endpoint_checks
