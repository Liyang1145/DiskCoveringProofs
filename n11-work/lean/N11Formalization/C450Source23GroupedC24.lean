import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((2856491507:ℚ)/5000000000),((1252924989:ℚ)/2000000000),((26715440549:ℚ)/53400000000),((1604924989:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3600738793:ℚ)/5000000000),((-57975960978909869219939323930846397:ℚ)/3172360500000000000000000000000000000),((-79486026384105824243723:ℚ)/216600000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((619135167:ℚ)/1000000000),((3251803541:ℚ)/5000000000),((811135167:ℚ)/1580000000),((1377267847:ℚ)/2225000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3093341189:ℚ)/5000000000),((-186676922943282080085061255505953301669297647970271:ℚ)/6162987500000000000000000000000000000000000000000000),((-169055525284418471423001:ℚ)/451250000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((1286072141:ℚ)/2000000000),((6742489893:ℚ)/10000000000),((11690504987:ℚ)/22880000000),((8502489893:ℚ)/13825000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2810853287:ℚ)/5000000000),((-52306030406389393745878334524510332954187662492182129:ℚ)/1701356800000000000000000000000000000000000000000000000),((-2039838022351797919492187:ℚ)/5415000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1667317149:ℚ)/2500000000),((6861897129:ℚ)/10000000000),((15031220043:ℚ)/29075000000),((8621897129:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5000984849:ℚ)/10000000000),((-342564405532577965128998740335111504739111657311840579:ℚ)/9601060467529296875000000000000000000000000000000000000),((-2059985025509146480304483:ℚ)/5415000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3394343873:ℚ)/5000000000),((1396256613:ℚ)/2000000000),((30480407111:ℚ)/59100000000),((1748256613:ℚ)/2907500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1165691463:ℚ)/2500000000),((-2875458567152487160489964025932080140561836554297794583:ℚ)/80634793359375000000000000000000000000000000000000000000),((-82605940229766466164347:ℚ)/216600000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6908085207:ℚ)/10000000000),((7100648723:ℚ)/10000000000),((61796596449:ℚ)/120100000000),((8860648723:ℚ)/14775000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((430017199:ℚ)/1000000000),((-96385942403769442188528565778216980183228416508413236073:ℚ)/2706755626562500000000000000000000000000000000000000000000),((-690048195835612674211609:ℚ)/1805000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((351373101:ℚ)/500000000),((360999753:ℚ)/500000000),((3131611707:ℚ)/6100000000),((448999753:ℚ)/750625000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((390638673:ℚ)/1000000000),((-12600506303116578907512798608078502581449664214642891:ℚ)/354657812500000000000000000000000000000000000000000000),((-273022816316990132393:ℚ)/712500000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((178670479:ℚ)/250000000),((7458633307:ℚ)/10000000000),((1586693353:ℚ)/3145000000),((9218633307:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1735385687:ℚ)/5000000000),((-22270033433778142738393629633112687954811615676937:ℚ)/714781103515625000000000000000000000000000000000000),((-689776523312751397591529:ℚ)/1805000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((3692739009:ℚ)/5000000000),((60134409:ℚ)/78125000),((1206265669:ℚ)/2400000000),((147768818:ℚ)/245703125),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((119080593:ℚ)/500000000),((-74461885187651319679674910035499379791640921436893:ℚ)/2400000000000000000000000000000000000000000000000000),((-1464211882145549:ℚ)/3800000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((152481369:ℚ)/200000000),((1200491501:ℚ)/1250000000),((1336169583:ℚ)/3200000000),((157832389:ℚ)/225000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4932017465887402300206550856903:ℚ)/400000000000000000000000000000000),((-6243713:ℚ)/16000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((9530917709:ℚ)/10000000000),((13411812621:ℚ)/10000000000),((80156423963:ℚ)/220800000000),((15171812621:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((13470508667911202098813751:ℚ)/253920000000000000000000000),((-6243713:ℚ)/16000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC24
#check @N11Formalization.C450Source23GroupedC24.bound
#print axioms N11Formalization.C450Source23GroupedC24.valid0
#print axioms N11Formalization.C450Source23GroupedC24.valid1
#print axioms N11Formalization.C450Source23GroupedC24.valid2
#print axioms N11Formalization.C450Source23GroupedC24.valid3
#print axioms N11Formalization.C450Source23GroupedC24.valid4
#print axioms N11Formalization.C450Source23GroupedC24.valid5
#print axioms N11Formalization.C450Source23GroupedC24.valid6
#print axioms N11Formalization.C450Source23GroupedC24.valid7
#print axioms N11Formalization.C450Source23GroupedC24.valid8
#print axioms N11Formalization.C450Source23GroupedC24.valid9
#print axioms N11Formalization.C450Source23GroupedC24.valid10
#print axioms N11Formalization.C450Source23GroupedC24.bound
#print axioms N11Formalization.C450Source23GroupedC24.endpoint_checks
