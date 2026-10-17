import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((8336307:ℚ)/12500000),((1376105621:ℚ)/2000000000),((-8928950589:ℚ)/19840000000),((-5536307:ℚ)/15796875),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((62519959:ℚ)/125000000),((528173854703880512047152825165018389755667:ℚ)/1995571639812096000000000000000000000000000),((14399940743401356969:ℚ)/64000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((13260047:ℚ)/19531250),((43753437:ℚ)/62500000),((-95260311:ℚ)/210625000),((-71080376:ℚ)/201171875),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1165357529:ℚ)/2500000000),((10245143099569529855670644577926982270715376492451971:ℚ)/38722575814914703369140625000000000000000000000000000),((1543872303212135953943:ℚ)/7050781250000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((172729799:ℚ)/250000000),((3530271559:ℚ)/5000000000),((-23132444031:ℚ)/51500000000),((-38909933:ℚ)/108281250),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1074169373:ℚ)/2500000000),((419478651416237208530095084130300930102800489618456273433939:ℚ)/1601504666207885742187500000000000000000000000000000000000000),((1967178704761843906018841:ℚ)/9241600000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((696919783:ℚ)/1000000000),((1780131237:ℚ)/2500000000),((-433377079:ℚ)/962500000),((-472919783:ℚ)/1311250000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4103037213:ℚ)/10000000000),((20860737970183105847363844522518031895418178490245628863:ℚ)/79642059680175781250000000000000000000000000000000000000),((31019781148173529038604249:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3514596047:ℚ)/5000000000),((179512393:ℚ)/250000000),((-1183611537:ℚ)/2622500000),((-2394596047:ℚ)/6615625000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3900404079:ℚ)/10000000000),((1812793978359741017155709692745681955005482536024182447069:ℚ)/6920625742583691406250000000000000000000000000000000000000),((764053654612404346253316169:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((7089175071:ℚ)/10000000000),((905056967:ℚ)/1250000000),((-5985512703:ℚ)/13231250000),((-4849175071:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1843645169:ℚ)/5000000000),((7509857378401647396950182218074735507454190604409246336763:ℚ)/28668347851018142700195312500000000000000000000000000000000),((3010195346554950084247815081:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((1787286767:ℚ)/2500000000),((3650202643:ℚ)/5000000000),((-8070607929:ℚ)/17800000000),((-1227286767:ℚ)/3367187500),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((692351039:ℚ)/2000000000),((1715375650648783385785284885464952124474292342099113041001341:ℚ)/6547787320450000000000000000000000000000000000000000000000000),((185245013175379232077437449:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((3604554191:ℚ)/5000000000),((7360344649:ℚ)/10000000000),((-48963101841:ℚ)/107750000000),((-2484554191:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3221184587:ℚ)/10000000000),((2420475415546375002528518429218747450568957958325902785248650589:ℚ)/9238276192663964843750000000000000000000000000000000000000000000),((729347281304925713045058121:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7269059297:ℚ)/10000000000),((463767131:ℚ)/625000000),((-3093904179:ℚ)/6793750000),((-1676353099:ℚ)/4568750000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((740477689:ℚ)/2500000000),((17150918013630474143859553364459333186425345839683729897559:ℚ)/65452083067758846282958984375000000000000000000000000000000),((2870602008727169711270944169:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7329000091:ℚ)/10000000000),((7480193887:ℚ)/10000000000),((-16680581661:ℚ)/36550000000),((-727000013:ℚ)/1975000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((26785009:ℚ)/100000000),((11607929711864183282343363221811177342611870571386612306323:ℚ)/44292264857031250000000000000000000000000000000000000000000),((2823558779953720936774273921:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7388931027:ℚ)/10000000000),((7719781381:ℚ)/10000000000),((-52198032429:ℚ)/110600000000),((-5148931027:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2362276167:ℚ)/10000000000),((511644091441887424890422358746512136168615023687040243876371:ℚ)/1900098350150000000000000000000000000000000000000000000000000),((2776259364475694856210153489:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((3814280603:ℚ)/5000000000),((8676893813:ℚ)/10000000000),((-60812044317:ℚ)/114400000000),((-2694280603:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2313794848028021689342825728929691463:ℚ)/7818525000000000000000000000000000000),((180580027:ℚ)/1024000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((8585818787:ℚ)/10000000000),((10587032693:ℚ)/10000000000),((-8667032693:ℚ)/14400000000),((-6345818787:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1459422116802343995827841192582463489:ℚ)/4500000000000000000000000000000000000),((180580027:ℚ)/1024000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((10496163917:ℚ)/10000000000),((14398896109:ℚ)/10000000000),((-112310064981:ℚ)/160000000000),((-2752054639:ℚ)/9200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((15927129766940988060041659:ℚ)/42320000000000000000000000),((180580027:ℚ)/1024000000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC08
#check @N11Formalization.C450Source29GroupedC08.bound
#print axioms N11Formalization.C450Source29GroupedC08.valid0
#print axioms N11Formalization.C450Source29GroupedC08.valid1
#print axioms N11Formalization.C450Source29GroupedC08.valid2
#print axioms N11Formalization.C450Source29GroupedC08.valid3
#print axioms N11Formalization.C450Source29GroupedC08.valid4
#print axioms N11Formalization.C450Source29GroupedC08.valid5
#print axioms N11Formalization.C450Source29GroupedC08.valid6
#print axioms N11Formalization.C450Source29GroupedC08.valid7
#print axioms N11Formalization.C450Source29GroupedC08.valid8
#print axioms N11Formalization.C450Source29GroupedC08.valid9
#print axioms N11Formalization.C450Source29GroupedC08.valid10
#print axioms N11Formalization.C450Source29GroupedC08.valid11
#print axioms N11Formalization.C450Source29GroupedC08.valid12
#print axioms N11Formalization.C450Source29GroupedC08.valid13
#print axioms N11Formalization.C450Source29GroupedC08.bound
#print axioms N11Formalization.C450Source29GroupedC08.endpoint_checks
