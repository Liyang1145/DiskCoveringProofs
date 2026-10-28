import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1316092253:ℚ)/2000000000),((6804572177:ℚ)/10000000000),((-25872005239:ℚ)/99200000000),((-1708276759:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2619745721:ℚ)/5000000000),((496759339146542986925854989857043950369:ℚ)/3050598400000000000000000000000000000000),((2546174872675946250376343:ℚ)/18483200000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((418856011:ℚ)/625000000),((6925705409:ℚ)/10000000000),((-26719937863:ℚ)/101100000000),((-556568033:ℚ)/3218750000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4911265223:ℚ)/10000000000),((33178809345148627227201248090716702940895457731925259527:ℚ)/201828970898437500000000000000000000000000000000000000000),((235319320833344134747667:ℚ)/1805000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3411418311:ℚ)/5000000000),((6986238389:ℚ)/10000000000),((-27143668723:ℚ)/103000000000),((-60185129:ℚ)/337500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1140451003:ℚ)/2500000000),((2167032268922326752447456717253883092396120893488385963:ℚ)/13338952636718750000000000000000000000000000000000000000),((14198438575033594109036367:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1376674621:ℚ)/2000000000),((7046749789:ℚ)/10000000000),((-9189082841:ℚ)/34650000000),((-1890023863:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4377517661:ℚ)/10000000000),((91870082660114847742162559766224184529977047515006271:ℚ)/562791796875000000000000000000000000000000000000000000),((6100440487279307309887:ℚ)/51200000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-7:ℚ)/16),((-3:ℚ)/8),((347194397:ℚ)/500000000),((3538498793:ℚ)/5000000000),((-13889491551:ℚ)/52450000000),((-481583191:ℚ)/2634375000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((4185740307:ℚ)/10000000000),((73198383135002630515261979464715847808014173877262110199:ℚ)/450906503515625000000000000000000000000000000000000000000),((133275827055388674461543:ℚ)/1155200000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6974137431:ℚ)/10000000000),((1776810053:ℚ)/2500000000),((-6997670371:ℚ)/26343750000),((-9722412293:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((4086712583:ℚ)/10000000000),((1115644074179015438960045596720812478363939387915018193:ℚ)/6855893405914306640625000000000000000000000000000000000),((52433931532488689789082447:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((3502190867:ℚ)/5000000000),((356873887:ℚ)/500000000),((-1410117209:ℚ)/5292500000),((-4906572601:ℚ)/26581250000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((498173027:ℚ)/1250000000),((56675009878315394581367576958177846465779171835985387:ℚ)/347451255358886718750000000000000000000000000000000000),((12888828273856921130791703:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((7034620923:ℚ)/10000000000),((7167710239:ℚ)/10000000000),((-28413971673:ℚ)/106325000000),((-9903862769:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3881574223:ℚ)/10000000000),((38384848430491809256652313194905853530487332236837056993:ℚ)/234766547476196289062500000000000000000000000000000000000),((50674474571765135842794183:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((1766213767:ℚ)/2500000000),((722816043:ℚ)/1000000000),((-2883712301:ℚ)/10680000000),((-2498641301:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((755015413:ℚ)/2000000000),((1890223764969309469357184113838042894560439147435050783:ℚ)/11420497800000000000000000000000000000000000000000000000),((3111963444743168775383903:ℚ)/28880000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((890663563:ℚ)/1250000000),((3644295661:ℚ)/5000000000),((-14630069627:ℚ)/53875000000),((-1271990689:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((888261333:ℚ)/2500000000),((81239256160900329635722545724009956879176066115462057067:ℚ)/488665716552734375000000000000000000000000000000000000000),((750291093331987422107263:ℚ)/7220000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7185742583:ℚ)/10000000000),((1837250859:ℚ)/2500000000),((-7420756013:ℚ)/27175000000),((-10357227749:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3316928099:ℚ)/10000000000),((1963386758470359487287587847840227177484653363740987399:ℚ)/11758717373657226562500000000000000000000000000000000000),((46236951022817651494377103:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7076326:ℚ)/9765625),((7409397273:ℚ)/10000000000),((-30105780911:ℚ)/109650000000),((-41165912:ℚ)/216015625),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((765865623:ℚ)/2500000000),((16066192805424777920801905719969224537809163216653727477:ℚ)/95809257421875000000000000000000000000000000000000000000),((339098906951697472441:ℚ)/3525390625000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((7306554731:ℚ)/10000000000),((7650799247:ℚ)/10000000000),((-31795594729:ℚ)/110600000000),((-10719664193:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1393956263:ℚ)/5000000000),((107251341649386221253848954086555910916735117919072525943:ℚ)/603972775000000000000000000000000000000000000000000000000),((42646886488501739428292647:ℚ)/462080000000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((3773984227:ℚ)/5000000000),((4307036057:ℚ)/5000000000),((-19269252399:ℚ)/57200000000),((-5721952681:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1170818709:ℚ)/10000000000),((31246836440256775403187497555597870525097788183990423999:ℚ)/146210350000000000000000000000000000000000000000000000000),((8839941372213839917955383:ℚ)/115520000000000000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((1702256229:ℚ)/2000000000),((1316617667:ℚ)/1250000000),((-721813741:ℚ)/1800000000),((-2866768687:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((865879881250222220707883789301307165172047054758167:ℚ)/3417187500000000000000000000000000000000000000000000),((9354407:ℚ)/128000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((10430206649:ℚ)/10000000000),((14354958161:ℚ)/10000000000),((-78724707127:ℚ)/160000000000),((-20090619947:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((170252348349913807107919197576269416229:ℚ)/512000000000000000000000000000000000000),((9354407:ℚ)/128000000)⟩
theorem valid15 : Valid source36 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC10
#check @N11Formalization.C450Source36GroupedC10.bound
#print axioms N11Formalization.C450Source36GroupedC10.valid0
#print axioms N11Formalization.C450Source36GroupedC10.valid1
#print axioms N11Formalization.C450Source36GroupedC10.valid2
#print axioms N11Formalization.C450Source36GroupedC10.valid3
#print axioms N11Formalization.C450Source36GroupedC10.valid4
#print axioms N11Formalization.C450Source36GroupedC10.valid5
#print axioms N11Formalization.C450Source36GroupedC10.valid6
#print axioms N11Formalization.C450Source36GroupedC10.valid7
#print axioms N11Formalization.C450Source36GroupedC10.valid8
#print axioms N11Formalization.C450Source36GroupedC10.valid9
#print axioms N11Formalization.C450Source36GroupedC10.valid10
#print axioms N11Formalization.C450Source36GroupedC10.valid11
#print axioms N11Formalization.C450Source36GroupedC10.valid12
#print axioms N11Formalization.C450Source36GroupedC10.valid13
#print axioms N11Formalization.C450Source36GroupedC10.valid14
#print axioms N11Formalization.C450Source36GroupedC10.valid15
#print axioms N11Formalization.C450Source36GroupedC10.bound
#print axioms N11Formalization.C450Source36GroupedC10.endpoint_checks
