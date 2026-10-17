import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((6211198913:ℚ)/10000000000),((1341489033:ℚ)/2000000000),((-893489033:ℚ)/9920000000),((-363732971:ℚ)/35600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((245660383:ℚ)/400000000),((45263709243347976339381380769353450607722149973870469237:ℚ)/2185403900000000000000000000000000000000000000000000000000),((-914155956497586370247833:ℚ)/221798400000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6686647713:ℚ)/10000000000),((1706581841:ℚ)/2500000000),((-382193947:ℚ)/4450000000),((-1566647713:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2476543061:ℚ)/5000000000),((14324935244230730173869937003838946103334233215531393073881:ℚ)/714428311043750000000000000000000000000000000000000000000000),((-773061801688568426234019:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3402750047:ℚ)/5000000000),((3472602507:ℚ)/5000000000),((-2352602507:ℚ)/27175000000),((-842750047:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4613316077:ℚ)/10000000000),((1075226035826087357810574232752857717191778538148551137099:ℚ)/53855025527050781250000000000000000000000000000000000000000),((-532496753229089993973787:ℚ)/72960000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((6924348953:ℚ)/10000000000),((1400928441:ℚ)/2000000000),((-952928441:ℚ)/11060000000),((-1804348953:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1062137279:ℚ)/2500000000),((5951603198816004415587778148058635356519393857417251469553:ℚ)/299842983018701171875000000000000000000000000000000000000000),((-1758536388816932504958457:ℚ)/221798400000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((6983772119:ℚ)/10000000000),((1412815669:ℚ)/2000000000),((-964815669:ℚ)/11155000000),((-207085791:ℚ)/12500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2027346487:ℚ)/5000000000),((2107681506704007106040690614906396416472736366723400017:ℚ)/106382369995117187500000000000000000000000000000000000000),((-608558045693187455869739:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((7043194469:ℚ)/10000000000),((7123513459:ℚ)/10000000000),((-4883513459:ℚ)/56250000000),((-1923194469:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3851659011:ℚ)/10000000000),((1353686278572422949253117145213260682540984948503009151:ℚ)/68447057279296875000000000000000000000000000000000000000),((-830160162902538938329401:ℚ)/97280000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((3551308013:ℚ)/5000000000),((7182947573:ℚ)/10000000000),((-4942947573:ℚ)/56725000000),((-991308013:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((727581381:ℚ)/2000000000),((52399321798077722602758293473045920754008397317109472140201:ℚ)/2654010273200000000000000000000000000000000000000000000000000),((-16331745998889082769299371:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((7162036809:ℚ)/10000000000),((905297589:ℚ)/1250000000),((-625297589:ℚ)/7150000000),((-2042036809:ℚ)/115350000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((106606823:ℚ)/312500000),((3168576317114655893722991405014781513507462012019369493:ℚ)/160749688783172607421875000000000000000000000000000000000),((-791721564683904700367137:ℚ)/86640000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7221456837:ℚ)/10000000000),((73018129:ℚ)/100000000),((-50618129:ℚ)/576750000),((-2101456837:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((792364897:ℚ)/2500000000),((148792454043680860706186943022761670233916467682846951520421:ℚ)/7560412671518750000000000000000000000000000000000000000000000),((-1744798543143514170659:ℚ)/184832000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/8),((-1:ℚ)/16),((227527379:ℚ)/312500000),((1437743:ℚ)/1953125),((-8001944:ℚ)/90859375),((-67527379:ℚ)/3664062500),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((290816707:ℚ)/1000000000),((21079295001089508159330448303708742143787553022002706063:ℚ)/1072678574028611183166503906250000000000000000000000000000),((-10989698691779742041:ℚ)/1128125000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7340294701:ℚ)/10000000000),((3710337257:ℚ)/5000000000),((-2590337257:ℚ)/29312500000),((-2220294701:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((524352257:ℚ)/2000000000),((7915723076173812595087616296010239721641902051979410431491:ℚ)/403388992912500000000000000000000000000000000000000000000000),((-4640667738923497569601651:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((1849928143:ℚ)/2500000000),((471220787:ℚ)/625000000),((-110406929:ℚ)/1231250000),((-569928143:ℚ)/30025000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2300877291:ℚ)/10000000000),((490688419256022818289920029748656931150085230301201583049:ℚ)/24995196489038085937500000000000000000000000000000000000000),((-74496877407293782362331:ℚ)/7220000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7518546279:ℚ)/10000000000),((7658387299:ℚ)/10000000000),((-5418387299:ℚ)/60050000000),((-2398546279:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1465386931:ℚ)/10000000000),((800685944101580990249554373101121423211508667588707080033029:ℚ)/40890627150000000000000000000000000000000000000000000000000000),((-266196512749031:ℚ)/24320000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((61099019:ℚ)/80000000),((8133775389:ℚ)/10000000000),((-5893775389:ℚ)/61000000000),((-20139019:ℚ)/1036800000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2795444564054705224672375353135925082373174750323261:ℚ)/141635970662400000000000000000000000000000000000000000),((-1458433:ℚ)/128000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((202816949:ℚ)/250000000),((2508739683:ℚ)/2500000000),((-1948739683:ℚ)/16200000000),((-74816949:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((219440410998101055790595823547664755857827407693130071:ℚ)/10800000000000000000000000000000000000000000000000000000),((-1458433:ℚ)/128000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10013594547:ℚ)/10000000000),((2767269469:ℚ)/2000000000),((-2319269469:ℚ)/16000000000),((-4893594547:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1121604675752298887512927103746863438077920993892871161153:ℚ)/50458982400000000000000000000000000000000000000000000000000),((-1458433:ℚ)/128000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC15
#check @N11Formalization.C450NinthGroupedC15.bound
#print axioms N11Formalization.C450NinthGroupedC15.valid0
#print axioms N11Formalization.C450NinthGroupedC15.valid1
#print axioms N11Formalization.C450NinthGroupedC15.valid2
#print axioms N11Formalization.C450NinthGroupedC15.valid3
#print axioms N11Formalization.C450NinthGroupedC15.valid4
#print axioms N11Formalization.C450NinthGroupedC15.valid5
#print axioms N11Formalization.C450NinthGroupedC15.valid6
#print axioms N11Formalization.C450NinthGroupedC15.valid7
#print axioms N11Formalization.C450NinthGroupedC15.valid8
#print axioms N11Formalization.C450NinthGroupedC15.valid9
#print axioms N11Formalization.C450NinthGroupedC15.valid10
#print axioms N11Formalization.C450NinthGroupedC15.valid11
#print axioms N11Formalization.C450NinthGroupedC15.valid12
#print axioms N11Formalization.C450NinthGroupedC15.valid13
#print axioms N11Formalization.C450NinthGroupedC15.valid14
#print axioms N11Formalization.C450NinthGroupedC15.valid15
#print axioms N11Formalization.C450NinthGroupedC15.bound
#print axioms N11Formalization.C450NinthGroupedC15.endpoint_checks
