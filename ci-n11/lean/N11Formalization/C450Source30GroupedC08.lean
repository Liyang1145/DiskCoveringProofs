import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((3341829517:ℚ)/5000000000),((1379607807:ℚ)/2000000000),((-8832470263:ℚ)/19840000000),((-2181829517:ℚ)/6318750000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((992270681:ℚ)/2000000000),((5649262156287895794683789384066027709067:ℚ)/21457759567872000000000000000000000000000),((175477932948027809861422907:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((1700965277:ℚ)/2500000000),((3509077459:ℚ)/5000000000),((-22621697131:ℚ)/50550000000),((-1120965277:ℚ)/3218750000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1154539597:ℚ)/2500000000),((15655333840328489379045714239254486170599348551680488164649:ℚ)/59477876451708984375000000000000000000000000000000000000000),((42728636282209224427001627:ℚ)/184832000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6924008659:ℚ)/10000000000),((3539096909:ℚ)/5000000000),((-22891872181:ℚ)/51500000000),((-1534669553:ℚ)/4331250000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4249635273:ℚ)/10000000000),((139124010881571711050458552618542871222190198527406813581693:ℚ)/533834888735961914062500000000000000000000000000000000000000),((665190880958239187590507003:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((3492031473:ℚ)/5000000000),((1427644099:ℚ)/2000000000),((-1323542413:ℚ)/2970000000),((-2332031473:ℚ)/6556250000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((253357671:ℚ)/625000000),((17568572299512903147883592936418510340916776438299675511:ℚ)/67406438756250000000000000000000000000000000000000000000),((163969255264179925479270627:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7044104721:ℚ)/10000000000),((1439647057:ℚ)/2000000000),((-9372823513:ℚ)/20980000000),((-4724104721:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((76969399:ℚ)/200000000),((923637452407271436341560404577689977649318428476143968770091:ℚ)/3543360380202850000000000000000000000000000000000000000000000),((646509660574182021289637283:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((888016791:ℚ)/1250000000),((453639907:ℚ)/625000000),((-2962759163:ℚ)/6615625000),((-598016791:ℚ)/1668750000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3632288209:ℚ)/10000000000),((934245107115389647610654401354560245564339990905862082673:ℚ)/3583543481377267837524414062500000000000000000000000000000),((9954512187838130802169203:ℚ)/46208000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((7164152101:ℚ)/10000000000),((7318230487:ℚ)/10000000000),((-47944074383:ℚ)/106800000000),((-4844152101:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1701544713:ℚ)/5000000000),((40975700515016785032434870032613299556764029692846238200700637:ℚ)/157146895690800000000000000000000000000000000000000000000000000),((627614360216190846913765963:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7224158357:ℚ)/10000000000),((922276439:ℚ)/1250000000),((-6060487951:ℚ)/13468750000),((-4904158357:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3158034431:ℚ)/10000000000),((4705699026425299312272042192985773959496610670691509360673149:ℚ)/18043508188796806335449218750000000000000000000000000000000000),((618086383442493591553658987:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((3642076703:ℚ)/5000000000),((937267733:ℚ)/1250000000),((-6195409597:ℚ)/13587500000),((-2482076703:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((115723603:ℚ)/400000000),((78892260003340584032324564894123638299391253377106580589967:ℚ)/299660133443395233154296875000000000000000000000000000000000),((152126207982529959135124867:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7404111061:ℚ)/10000000000),((1934470821:ℚ)/2500000000),((-163673891:ℚ)/350000000),((-5084111061:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2275361587:ℚ)/10000000000),((16141449577915143223432821014806945030725666607185859:ℚ)/60216406250000000000000000000000000000000000000000000),((589180937903488582375327723:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((238872009:ℚ)/312500000),((8695519103:ℚ)/10000000000),((-60339671927:ℚ)/114400000000),((-166372009:ℚ)/506250000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1498413644900877557918967182728753:ℚ)/5090185546875000000000000000000000),((38583769:ℚ)/204800000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((1075214529:ℚ)/1250000000),((5303200781:ℚ)/5000000000),((-38768807029:ℚ)/64800000000),((-785214529:ℚ)/2500000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((204200737890472510269153088093950731:ℚ)/632812500000000000000000000000000000),((38583769:ℚ)/204800000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((2628212209:ℚ)/2500000000),((14419131989:ℚ)/10000000000),((-111852187901:ℚ)/160000000000),((-682737403:ℚ)/2300000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((996006583659002704153319:ℚ)/2645000000000000000000000),((38583769:ℚ)/204800000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC08
#check @N11Formalization.C450Source30GroupedC08.bound
#print axioms N11Formalization.C450Source30GroupedC08.valid0
#print axioms N11Formalization.C450Source30GroupedC08.valid1
#print axioms N11Formalization.C450Source30GroupedC08.valid2
#print axioms N11Formalization.C450Source30GroupedC08.valid3
#print axioms N11Formalization.C450Source30GroupedC08.valid4
#print axioms N11Formalization.C450Source30GroupedC08.valid5
#print axioms N11Formalization.C450Source30GroupedC08.valid6
#print axioms N11Formalization.C450Source30GroupedC08.valid7
#print axioms N11Formalization.C450Source30GroupedC08.valid8
#print axioms N11Formalization.C450Source30GroupedC08.valid9
#print axioms N11Formalization.C450Source30GroupedC08.valid10
#print axioms N11Formalization.C450Source30GroupedC08.valid11
#print axioms N11Formalization.C450Source30GroupedC08.valid12
#print axioms N11Formalization.C450Source30GroupedC08.bound
#print axioms N11Formalization.C450Source30GroupedC08.endpoint_checks
