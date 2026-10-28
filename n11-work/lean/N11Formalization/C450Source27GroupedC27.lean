import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((2719415053:ℚ)/5000000000),((3002098393:ℚ)/5000000000),((1173138351:ℚ)/1780000000),((41343082323:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3866313729:ℚ)/5000000000),((-263037409310766122556578455472491:ℚ)/1409938000000000000000000000000000),((-38956919190818467490957529:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((2958568831:ℚ)/5000000000),((6123752781:ℚ)/10000000000),((3758568831:ℚ)/5435000000),((84001280591:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3392056147:ℚ)/5000000000),((-221443148443479771481630854714860233520155373334351753:ℚ)/1003410549218750000000000000000000000000000000000000000),((-466914170824196461074608243:ℚ)/1108992000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((301832079:ℚ)/500000000),((624328081:ℚ)/1000000000),((381832079:ℚ)/553000000),((8531608891:ℚ)/10870000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3264750763:ℚ)/5000000000),((-14560064173078477585422341896495182215471247140913:ℚ)/66059522265625000000000000000000000000000000000000),((-1550463879229217818156681:ℚ)/3696640000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((6156119357:ℚ)/10000000000),((6362782309:ℚ)/10000000000),((2585373119:ℚ)/3750000000),((86630605399:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6266174309:ℚ)/10000000000),((-24182224807756646521128748847871246637917042053115931:ℚ)/109863281250000000000000000000000000000000000000000000),((-154440918488345218094752001:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((1568893083:ℚ)/2500000000),((810282327:ℚ)/1250000000),((1968893083:ℚ)/2860000000),((10993105597:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5992954987:ℚ)/10000000000),((-2921574688029581589210952118582984588279373389771639:ℚ)/13291850000000000000000000000000000000000000000000000),((-7210389886124271521094827:ℚ)/17328000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((1598750439:ℚ)/2500000000),((1635496929:ℚ)/2500000000),((1998750439:ℚ)/2883750000),((22150466219:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((228335843:ℚ)/400000000),((-2806949720198815919836831817071382257953169766107019:ℚ)/12490263308715820312500000000000000000000000000000000),((-28794648772345245368860283:ℚ)/69312000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6454708003:ℚ)/10000000000),((6601710981:ℚ)/10000000000),((8054708003:ℚ)/11630000000),((89258820791:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((695164317:ℚ)/1250000000),((-88288368332661149007347073181316028600851289069742061:ℚ)/393259436750000000000000000000000000000000000000000000),((-459759593615173601138037443:ℚ)/1108992000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((1302881759:ℚ)/2000000000),((6661428553:ℚ)/10000000000),((1622881759:ℚ)/2345000000),((89915714083:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5410680839:ℚ)/10000000000),((-645553767866300467404014630921017580623282158336879:ℚ)/2878395898437500000000000000000000000000000000000000),((-152931487266073971235580089:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1314820853:ℚ)/2000000000),((6721140571:ℚ)/10000000000),((1634820853:ℚ)/2364000000),((12938935183:ℚ)/16750000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1051237227:ℚ)/2000000000),((-1541618266679008267673091455916841849504866718595713:ℚ)/6880835700000000000000000000000000000000000000000000),((-152606328529725765953061761:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3316897271:ℚ)/5000000000),((10688357:ℚ)/15625000),((4116897271:ℚ)/6005000000),((47857309:ℚ)/61562500),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5097475857:ℚ)/10000000000),((-296108825810208500878446020854932757414435654571814153:ℚ)/1353377813281250000000000000000000000000000000000000000),((-2966427338034445530607:ℚ)/7220000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((422072501:ℚ)/625000000),((6959935731:ℚ)/10000000000),((522072501:ℚ)/762500000),((93199293041:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((238284911:ℚ)/500000000),((-605219211085392703954629870678888724889108155894963:ℚ)/2770764160156250000000000000000000000000000000000000),((-453619917992915112550323443:ℚ)/1108992000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((274900247:ℚ)/400000000),((7198652043:ℚ)/10000000000),((338900247:ℚ)/503200000),((95825172473:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2205563877:ℚ)/5000000000),((-41563405385637311849421288148112959462607379036929:ℚ)/199086551200000000000000000000000000000000000000000),((-449061792138999601385410787:ℚ)/1108992000000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7111144083:ℚ)/10000000000),((58103879:ℚ)/78125000),((8711144083:ℚ)/12960000000),((769142669:ℚ)/982812500),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3606239133:ℚ)/10000000000),((-34993649252785252235180981045415015372278870311331189:ℚ)/167961600000000000000000000000000000000000000000000000),((-144767491858754891466651:ℚ)/361000000000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((734971481:ℚ)/1000000000),((9344484693:ℚ)/10000000000),((894971481:ℚ)/1600000000),((119429331623:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2573504301:ℚ)/10000000000),((-189084401402778857668290051814256701969978674980007:ℚ)/1600000000000000000000000000000000000000000000000000),((-1938246714265147:ℚ)/4864000000000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((1851288093:ℚ)/2000000000),((3288225877:ℚ)/2500000000),((2171288093:ℚ)/4416000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-537139761345197970461501:ℚ)/9750528000000000000000000),((-2044011:ℚ)/5120000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC27
#check @N11Formalization.C450Source27GroupedC27.bound
#print axioms N11Formalization.C450Source27GroupedC27.valid0
#print axioms N11Formalization.C450Source27GroupedC27.valid1
#print axioms N11Formalization.C450Source27GroupedC27.valid2
#print axioms N11Formalization.C450Source27GroupedC27.valid3
#print axioms N11Formalization.C450Source27GroupedC27.valid4
#print axioms N11Formalization.C450Source27GroupedC27.valid5
#print axioms N11Formalization.C450Source27GroupedC27.valid6
#print axioms N11Formalization.C450Source27GroupedC27.valid7
#print axioms N11Formalization.C450Source27GroupedC27.valid8
#print axioms N11Formalization.C450Source27GroupedC27.valid9
#print axioms N11Formalization.C450Source27GroupedC27.valid10
#print axioms N11Formalization.C450Source27GroupedC27.valid11
#print axioms N11Formalization.C450Source27GroupedC27.valid12
#print axioms N11Formalization.C450Source27GroupedC27.valid13
#print axioms N11Formalization.C450Source27GroupedC27.valid14
#print axioms N11Formalization.C450Source27GroupedC27.bound
#print axioms N11Formalization.C450Source27GroupedC27.endpoint_checks
