import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/16),(0:ℚ),((190086329:ℚ)/312500000),((256201599:ℚ)/400000000),((486198401:ℚ)/4120000000),((6:ℚ)/31),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3214475233:ℚ)/5000000000),((-22248785635383741546921194184162135589164122984414027:ℚ)/437090800000000000000000000000000000000000000000000000),((-6535943316943827:ℚ)/30400000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6324666491:ℚ)/10000000000),((6525721703:ℚ)/10000000000),((12034278297:ℚ)/104900000000),((96:ℚ)/515),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1469363403:ℚ)/2500000000),((-88164140646702018088323439913103874414398976777298310219:ℚ)/1803626014062500000000000000000000000000000000000000000000),((-219339655921241833:ℚ)/972800000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((6445495639:ℚ)/10000000000),((3323166537:ℚ)/5000000000),((5956833463:ℚ)/53400000000),((192:ℚ)/1049),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((698029237:ℚ)/1250000000),((-412561465607126063331534088769809922134513140289980807:ℚ)/8812112500000000000000000000000000000000000000000000000),((-224429216822619357:ℚ)/972800000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6566248927:ℚ)/10000000000),((6766877891:ℚ)/10000000000),((11793122109:ℚ)/108700000000),((16:ℚ)/89),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1055349923:ℚ)/2000000000),((-359993441444639452677962043457320591360532402547461898223:ℚ)/8027284393750000000000000000000000000000000000000000000000),((-229515582351883701:ℚ)/972800000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((208966577:ℚ)/312500000),((3443679843:ℚ)/5000000000),((5836320157:ℚ)/55300000000),((192:ℚ)/1087),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4952303321:ℚ)/10000000000),((-14479564089432468427640206006299319032284326572956071:ℚ)/337038378906250000000000000000000000000000000000000000),((-7331216424630651:ℚ)/30400000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((3403772033:ℚ)/5000000000),((3503890871:ℚ)/5000000000),((5776109129:ℚ)/56250000000),((96:ℚ)/553),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((921454127:ℚ)/2000000000),((-2207804038926988201368952154413243626440874775697843:ℚ)/53644180297851562500000000000000000000000000000000000),((-119839703634460779:ℚ)/486400000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((3464046641:ℚ)/5000000000),((89101839:ℚ)/125000000),((142898161:ℚ)/1430000000),((64:ℚ)/375),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((6778529:ℚ)/16000000),((-720573028208953086066505291439440018153904757254347:ℚ)/18276293750000000000000000000000000000000000000000000),((-122378588442476283:ℚ)/486400000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((1409716283:ℚ)/2000000000),((3684359529:ℚ)/5000000000),((5595640471:ℚ)/59100000000),((24:ℚ)/143),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3832749199:ℚ)/10000000000),((-1293498116056289377358527836526567088399594667715014013:ℚ)/35837685937500000000000000000000000000000000000000000000),((-49966474713023529:ℚ)/194560000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((3644693273:ℚ)/5000000000),((3804548067:ℚ)/5000000000),((5475451933:ℚ)/61000000000),((32:ℚ)/197),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((286885557:ℚ)/1000000000),((-46952290056523041169368589901490293039004413371472180479:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-129987779191654899:ℚ)/486400000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((7529981737:ℚ)/10000000000),((8089335803:ℚ)/10000000000),((1163407133:ℚ)/14400000000),((48:ℚ)/305),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((271692629:ℚ)/2000000000),((-19089723609421911739520623813066728853418262018517357:ℚ)/691200000000000000000000000000000000000000000000000000),((-270109900116589731:ℚ)/972800000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((8010617951:ℚ)/10000000000),((2501314183:ℚ)/2500000000),((2138685817:ℚ)/40000000000),((4:ℚ)/27),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-4629261339388910884760525054640390459247581847182859891:ℚ)/400000000000000000000000000000000000000000000000000000000),((-35928843:ℚ)/128000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((4963869457:ℚ)/5000000000),((215997673:ℚ)/156250000),((74002327:ℚ)/3450000000),((3:ℚ)/25),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((20182620970071630413837473713412851329691722512657:ℚ)/2376367187500000000000000000000000000000000000000000),((-35928843:ℚ)/128000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC16
#check @N11Formalization.C450Source31GroupedC16.bound
#print axioms N11Formalization.C450Source31GroupedC16.valid0
#print axioms N11Formalization.C450Source31GroupedC16.valid1
#print axioms N11Formalization.C450Source31GroupedC16.valid2
#print axioms N11Formalization.C450Source31GroupedC16.valid3
#print axioms N11Formalization.C450Source31GroupedC16.valid4
#print axioms N11Formalization.C450Source31GroupedC16.valid5
#print axioms N11Formalization.C450Source31GroupedC16.valid6
#print axioms N11Formalization.C450Source31GroupedC16.valid7
#print axioms N11Formalization.C450Source31GroupedC16.valid8
#print axioms N11Formalization.C450Source31GroupedC16.valid9
#print axioms N11Formalization.C450Source31GroupedC16.valid10
#print axioms N11Formalization.C450Source31GroupedC16.valid11
#print axioms N11Formalization.C450Source31GroupedC16.bound
#print axioms N11Formalization.C450Source31GroupedC16.endpoint_checks
