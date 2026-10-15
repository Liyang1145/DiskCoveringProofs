import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((6688983653:ℚ)/10000000000),((3447672507:ℚ)/5000000000),((-2679672507:ℚ)/4960000000),((-44200852877:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2473307813:ℚ)/5000000000),((138649285477480774997086709422448612536928657856769764053929:ℚ)/600643017393750000000000000000000000000000000000000000000000),((2240324172543000384571739:ℚ)/7393280000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6808700147:ℚ)/10000000000),((7014994623:ℚ)/10000000000),((-1826331541:ℚ)/3370000000),((-45278301323:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((115096201:ℚ)/250000000),((1596431201133634184188869887434261005145053635030585488461673:ℚ)/6904668731250000000000000000000000000000000000000000000000000),((2215572023636000305332939:ℚ)/7393280000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((6928380563:ℚ)/10000000000),((3537403479:ℚ)/5000000000),((-2769403479:ℚ)/5150000000),((-6622203581:ℚ)/14850000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4235661039:ℚ)/10000000000),((2974095651760132749937580933124700695570613449367509481:ℚ)/13066897851562500000000000000000000000000000000000000000),((2190570553181924624831499:ℚ)/7393280000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((698820787:ℚ)/1000000000),((3567305643:ℚ)/5000000000),((-933101881:ℚ)/1732500000),((-4689387083:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4039870791:ℚ)/10000000000),((284760710029622890555709228640172528388559546592821266071:ℚ)/1249912827745312500000000000000000000000000000000000000000),((21779762623456694541899:ℚ)/73932800000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((1762006723:ℚ)/2500000000),((1791127629:ℚ)/2500000000),((-1407127629:ℚ)/2622500000),((-11858060507:ℚ)/26343750000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((1917349917:ℚ)/5000000000),((90335589553396504566058610419026774549588772763981812241:ℚ)/399546232378005981445312500000000000000000000000000000000),((135332473189908265124459:ℚ)/462080000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((884741671:ℚ)/1250000000),((287776313:ℚ)/400000000),((-226336313:ℚ)/421500000),((-5962675039:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((58251779:ℚ)/156250000),((2760737346784174198867970985660103110798638090352098319493:ℚ)/12204225344480895996093750000000000000000000000000000000000),((33733872160190474885411:ℚ)/115520000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((222119933:ℚ)/312500000),((180607581:ℚ)/250000000),((-142207581:ℚ)/264625000),((-1499079397:ℚ)/3322656250),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1809273899:ℚ)/5000000000),((54923872020738297947300398404449793257474637764120678847:ℚ)/242676162601126730442047119140625000000000000000000000000),((2102148884293479821419:ℚ)/7220000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((1427548077:ℚ)/2000000000),((3627098393:ℚ)/5000000000),((-2859098393:ℚ)/5316250000),((-9647932693:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((350572161:ℚ)/1000000000),((14664542356275806269558580035831278810962057435398908193129:ℚ)/64761836191200000000000000000000000000000000000000000000000),((257546098299637384802977:ℚ)/887193600000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7167640981:ℚ)/10000000000),((7284088489:ℚ)/10000000000),((-5748088489:ℚ)/10680000000),((-48508768829:ℚ)/107275000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3389309073:ℚ)/10000000000),((7292354885588246598535719646192754355889362561614536934327:ℚ)/32188954748011779785156250000000000000000000000000000000000),((2139818900772741515879931:ℚ)/7393280000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((7197539669:ℚ)/10000000000),((7313978373:ℚ)/10000000000),((-5777978373:ℚ)/10727500000),((-48777857021:ℚ)/107750000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3268926391:ℚ)/10000000000),((89112867173471164216011369580710867580071759271340280014797:ℚ)/393162110573959350585937500000000000000000000000000000000000),((2133404700081856522731131:ℚ)/7393280000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((289097459:ℚ)/400000000),((7373752781:ℚ)/10000000000),((-5837752781:ℚ)/10775000000),((-1961877131:ℚ)/4348000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((786029217:ℚ)/2500000000),((50623938124669094130108207471277224688206472020703673829:ℚ)/221424612717200000000000000000000000000000000000000000000),((3403159809962519848651:ℚ)/11829248000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7287224543:ℚ)/10000000000),((7433520199:ℚ)/10000000000),((-5897520199:ℚ)/10870000000),((-49585020887:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2878891781:ℚ)/10000000000),((170778399019288161329512656127035467516342117888676288823003:ℚ)/746370083525976562500000000000000000000000000000000000000000),((2114068379051693211208979:ℚ)/7393280000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7347005379:ℚ)/10000000000),((749328081:ℚ)/1000000000),((-198576027:ℚ)/365500000),((-50123048411:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((517494839:ℚ)/2000000000),((66346590660033084626615510583012415532675103156036559227923:ℚ)/289737064657031250000000000000000000000000000000000000000000),((6303298127796683138394433:ℚ)/22179840000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7406779173:ℚ)/10000000000),((966532327:ℚ)/1250000000),((-774532327:ℚ)/1382500000),((-50661012557:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2259745901:ℚ)/10000000000),((3116935261903624957954045732961542692841555914816292483:ℚ)/12988953565478515625000000000000000000000000000000000000),((6264203560776362926040977:ℚ)/22179840000000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((3822903741:ℚ)/5000000000),((8483688:ℚ)/9765625),((-6983688:ℚ)/11171875),((-26406133669:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((612709989547590422763664771646549423859154984106033:ℚ)/2183689599609375000000000000000000000000000000000000),((17706933:ℚ)/64000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((8601017303:ℚ)/10000000000),((10594484693:ℚ)/10000000000),((-9058484693:ℚ)/12960000000),((-61409155727:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13134005963879685020457755899310726874489696687234992119:ℚ)/40814668800000000000000000000000000000000000000000000000),((17706933:ℚ)/64000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((2627112557:ℚ)/2500000000),((3600725877:ℚ)/2500000000),((-3216725877:ℚ)/4000000000),((-19644013013:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((188883349371894550433483380474797693858811009263427732717:ℚ)/476100000000000000000000000000000000000000000000000000000),((17706933:ℚ)/64000000)⟩
theorem valid16 : Valid source26 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC07
#check @N11Formalization.C450Source26GroupedC07.bound
#print axioms N11Formalization.C450Source26GroupedC07.valid0
#print axioms N11Formalization.C450Source26GroupedC07.valid1
#print axioms N11Formalization.C450Source26GroupedC07.valid2
#print axioms N11Formalization.C450Source26GroupedC07.valid3
#print axioms N11Formalization.C450Source26GroupedC07.valid4
#print axioms N11Formalization.C450Source26GroupedC07.valid5
#print axioms N11Formalization.C450Source26GroupedC07.valid6
#print axioms N11Formalization.C450Source26GroupedC07.valid7
#print axioms N11Formalization.C450Source26GroupedC07.valid8
#print axioms N11Formalization.C450Source26GroupedC07.valid9
#print axioms N11Formalization.C450Source26GroupedC07.valid10
#print axioms N11Formalization.C450Source26GroupedC07.valid11
#print axioms N11Formalization.C450Source26GroupedC07.valid12
#print axioms N11Formalization.C450Source26GroupedC07.valid13
#print axioms N11Formalization.C450Source26GroupedC07.valid14
#print axioms N11Formalization.C450Source26GroupedC07.valid15
#print axioms N11Formalization.C450Source26GroupedC07.valid16
#print axioms N11Formalization.C450Source26GroupedC07.bound
#print axioms N11Formalization.C450Source26GroupedC07.endpoint_checks
