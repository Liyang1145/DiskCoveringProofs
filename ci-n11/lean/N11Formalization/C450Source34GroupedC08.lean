import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6740098357:ℚ)/10000000000),((1741571413:ℚ)/2500000000),((-10554142717:ℚ)/24800000000),((-4100098357:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((960605637:ℚ)/2000000000),((5342605524603043198773962784441252231:ℚ)/19066240000000000000000000000000000000),((4005053592154094866301929481:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((857594463:ℚ)/1250000000),((1756639497:ℚ)/2500000000),((-10689755473:ℚ)/25275000000),((-527594463:ℚ)/1594531250),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2223601681:ℚ)/5000000000),((1747462374618066129421375538424785805473855995374310321:ℚ)/6307155340576171875000000000000000000000000000000000000),((61047714436534224906794961:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((1384211423:ℚ)/2000000000),((7086813401:ℚ)/10000000000),((-43301320609:ℚ)/102050000000),((-856211423:ℚ)/2575000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((851809031:ℚ)/2000000000),((16993635235867328255735001445263631651665600796129769423:ℚ)/61313617218750000000000000000000000000000000000000000000),((154304184564596410518427601:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6981341043:ℚ)/10000000000),((7147052369:ℚ)/10000000000),((-43843471321:ℚ)/103000000000),((-160790409:ℚ)/481250000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((507849351:ℚ)/1250000000),((7396882277656329686265482641032402381010226296976410297:ℚ)/26677905273437500000000000000000000000000000000000000000),((3807855859678543711648689081:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((352080399:ℚ)/500000000),((7207275351:ℚ)/10000000000),((-4035043469:ℚ)/9450000000),((-220080399:ℚ)/655625000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((154288451:ℚ)/400000000),((69667949377754957227649489805972673407338147800270657:ℚ)/251163281250000000000000000000000000000000000000000000),((9394518309756365590752369:ℚ)/36966400000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((1775464601:ℚ)/2500000000),((7267482791:ℚ)/10000000000),((-44927345119:ℚ)/104900000000),((-15280337:ℚ)/45312500),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((455088437:ℚ)/1250000000),((2002051429193523500823049380794381517465406521894381259463:ℚ)/7214504056250000000000000000000000000000000000000000000000),((231716179467122669867962369:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((7162092771:ℚ)/10000000000),((3663837557:ℚ)/5000000000),((-22734538013:ℚ)/52925000000),((-1507364257:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3411198239:ℚ)/10000000000),((192928402811805946317095303994554700140296764611502074863:ℚ)/694902510717773437500000000000000000000000000000000000000),((3656810375612448361308739929:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((3611155761:ℚ)/5000000000),((7387852731:ℚ)/10000000000),((-46010674579:ℚ)/106800000000),((-2291155761:ℚ)/6734375000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1582924649:ℚ)/5000000000),((6344570679100469424321508307747483095292168006956379826641:ℚ)/22840995600000000000000000000000000000000000000000000000000),((901465428177145563781956849:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7282515081:ℚ)/10000000000),((7448016039:ℚ)/10000000000),((-46552144351:ℚ)/107750000000),((-4642515081:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((362579581:ℚ)/1250000000),((2172926722578413326460928652844404799484651530515154124407:ℚ)/7818651464843750000000000000000000000000000000000000000000),((3554612764427876459517130209:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((367135193:ℚ)/500000000),((3784150619:ℚ)/5000000000),((-23817355571:ℚ)/54350000000),((-235135193:ℚ)/691250000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((652375687:ℚ)/2500000000),((52866701887887174541199278532851807288676778472317336841:ℚ)/188139477978515625000000000000000000000000000000000000000),((8757658534658214928727681:ℚ)/36966400000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((1492607727:ℚ)/2000000000),((7808715839:ℚ)/10000000000),((-49798442551:ℚ)/110600000000),((-964607727:ℚ)/2860000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((118834251:ℚ)/625000000),((346578474113025863045917884749461750802370159301100775641:ℚ)/1207945550000000000000000000000000000000000000000000000000),((135962522969940221133518001:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((1540709453:ℚ)/2000000000),((438431947:ℚ)/500000000),((-2921887523:ℚ)/5720000000),((-1012709453:ℚ)/3240000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((7807089423395334456637316906849359:ℚ)/24538800000000000000000000000000000),((227089403:ℚ)/1024000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((4331894813:ℚ)/5000000000),((10682766913:ℚ)/10000000000),((-75664902217:ℚ)/129600000000),((-3011894813:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((164121740259731351600408915263178023:ℚ)/466560000000000000000000000000000000),((227089403:ℚ)/1024000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((2115674017:ℚ)/2000000000),((7249638371:ℚ)/5000000000),((-55006745339:ℚ)/80000000000),((-1587674017:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((338374340854414606075626291199410557:ℚ)/800000000000000000000000000000000000),((227089403:ℚ)/1024000000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source34 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC08
#check @N11Formalization.C450Source34GroupedC08.bound
#print axioms N11Formalization.C450Source34GroupedC08.valid0
#print axioms N11Formalization.C450Source34GroupedC08.valid1
#print axioms N11Formalization.C450Source34GroupedC08.valid2
#print axioms N11Formalization.C450Source34GroupedC08.valid3
#print axioms N11Formalization.C450Source34GroupedC08.valid4
#print axioms N11Formalization.C450Source34GroupedC08.valid5
#print axioms N11Formalization.C450Source34GroupedC08.valid6
#print axioms N11Formalization.C450Source34GroupedC08.valid7
#print axioms N11Formalization.C450Source34GroupedC08.valid8
#print axioms N11Formalization.C450Source34GroupedC08.valid9
#print axioms N11Formalization.C450Source34GroupedC08.valid10
#print axioms N11Formalization.C450Source34GroupedC08.valid11
#print axioms N11Formalization.C450Source34GroupedC08.valid12
#print axioms N11Formalization.C450Source34GroupedC08.valid13
#print axioms N11Formalization.C450Source34GroupedC08.bound
#print axioms N11Formalization.C450Source34GroupedC08.endpoint_checks
