import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((6234703141:ℚ)/10000000000),((1625124631:ℚ)/2500000000),((-3435373893:ℚ)/24800000000),((-3034703141:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6087636143:ℚ)/10000000000),((2534245509409124643122537786956095933949909102340525623913:ℚ)/79393446093750000000000000000000000000000000000000000000000),((1641259047825110329075283:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((3236291811:ℚ)/5000000000),((3369213149:ℚ)/5000000000),((-7227639447:ℚ)/51500000000),((-1636291811:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5516598997:ℚ)/10000000000),((96869422363533177712240900514473015702659158415714218093:ℚ)/3063310607812500000000000000000000000000000000000000000000),((3104047084905815790257403:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6710436967:ℚ)/10000000000),((6857378941:ℚ)/10000000000),((-4937378941:ℚ)/35600000000),((-3510436967:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((122170577:ℚ)/250000000),((2782281320994945413277938724848592343387076135476829062807:ℚ)/89303538880468750000000000000000000000000000000000000000000),((-1746135937003232615922757:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((1707338589:ℚ)/2500000000),((1744081151:ℚ)/2500000000),((-3792243453:ℚ)/27175000000),((-907338589:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2271148753:ℚ)/5000000000),((26125431806710589732640493518086688752202083904058095121:ℚ)/841484773860168457031250000000000000000000000000000000000),((-540749962752209953096797:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((3474132991:ℚ)/5000000000),((7035794929:ℚ)/10000000000),((-2192483541:ℚ)/15800000000),((-1874132991:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4171545017:ℚ)/10000000000),((20643651618569699484377428920277451546419712817721054681:ℚ)/669292372809600830078125000000000000000000000000000000000),((-15727091683957482353094077:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((3503859863:ℚ)/5000000000),((3547631821:ℚ)/5000000000),((-7762895463:ℚ)/55775000000),((-1903859863:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3974051223:ℚ)/10000000000),((111960715399016421978604424732429561525508962061864824051:ℚ)/3635285049676895141601562500000000000000000000000000000000),((-4794010297778092647311077:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((7067172137:ℚ)/10000000000),((7154730781:ℚ)/10000000000),((-5234730781:ℚ)/37500000000),((-3867172137:ℚ)/56725000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3766797299:ℚ)/10000000000),((263133257593894783030018885304882924107137160103148331:ℚ)/8555882159912109375000000000000000000000000000000000000),((-22623437263589934985533317:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((28506493:ℚ)/40000000),((3607098193:ℚ)/5000000000),((-7941294579:ℚ)/56725000000),((-1427863:ℚ)/20800000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3548069161:ℚ)/10000000000),((3919455561371652191180367836266632524941360709243:ℚ)/127615820800000000000000000000000000000000000000000),((-6517320507954349104413053:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((898259137:ℚ)/1250000000),((1454732099:ℚ)/2000000000),((-3212196297:ℚ)/22880000000),((-166086379:ℚ)/2403125000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3315592377:ℚ)/10000000000),((4053135430524931750321606948139854800812489717269:ℚ)/132139829926192760467529296875000000000000000000000),((-1180543095378910709913797:ℚ)/295731200000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7245521707:ℚ)/10000000000),((3666561573:ℚ)/5000000000),((-2706561573:ℚ)/19225000000),((-4045521707:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3066236673:ℚ)/10000000000),((28951712594365169342898380381690808726565270104802080508643:ℚ)/945051583939843750000000000000000000000000000000000000000000),((-8239081316854661471401813:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((7304969113:ℚ)/10000000000),((7392584373:ℚ)/10000000000),((-16417753119:ℚ)/116300000000),((-586424159:ℚ)/8375000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((139774193:ℚ)/500000000),((391958564376069683074780645096962268228187725102501920799:ℚ)/12809596032714843750000000000000000000000000000000000000000),((-36397527513165237335255413:ℚ)/7393280000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((460275959:ℚ)/625000000),((7452044211:ℚ)/10000000000),((-16596132633:ℚ)/117250000000),((-86758653:ℚ)/1231250000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((499275187:ℚ)/2000000000),((41806740528560191424796959437162802829858291956688353:ℚ)/1367828345108032226562500000000000000000000000000000000),((-39837185947731083209777637:ℚ)/7393280000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((1855965107:ℚ)/2500000000),((1892739963:ℚ)/2500000000),((-1412739963:ℚ)/9850000000),((-1055965107:ℚ)/15012500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((33705367:ℚ)/156250000),((31896589859881675562101408510354374067633939162556328231:ℚ)/1041466520376586914062500000000000000000000000000000000000),((-2693003501356657590428693:ℚ)/462080000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7542747263:ℚ)/10000000000),((7689870323:ℚ)/10000000000),((-17309610969:ℚ)/120100000000),((-4342747263:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1228228991:ℚ)/10000000000),((52074229538549345622551789957694220974660295128324708079927:ℚ)/1703776131250000000000000000000000000000000000000000000000000),((-3305502759581791:ℚ)/486400000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((766162983:ℚ)/1000000000),((8165465069:ℚ)/10000000000),((-18736395207:ℚ)/122000000000),((-446162983:ℚ)/6480000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1073474982215835002509238840669380144757277581519064289:ℚ)/34579094400000000000000000000000000000000000000000000000),((-3721183:ℚ)/512000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((4068560583:ℚ)/5000000000),((10067278271:ℚ)/10000000000),((-8147278271:ℚ)/43200000000),((-2468560583:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((353248201552965173669060244799207250740148554500084594589:ℚ)/10800000000000000000000000000000000000000000000000000000000),((-3721183:ℚ)/512000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((2509654803:ℚ)/2500000000),((13869405571:ℚ)/10000000000),((-35848216713:ℚ)/160000000000),((-1709654803:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3565623986266124668202247520436300245182439907743890121:ℚ)/98552700000000000000000000000000000000000000000000000000),((-3721183:ℚ)/512000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC14
#check @N11Formalization.C450Source11GroupedC14.bound
#print axioms N11Formalization.C450Source11GroupedC14.valid0
#print axioms N11Formalization.C450Source11GroupedC14.valid1
#print axioms N11Formalization.C450Source11GroupedC14.valid2
#print axioms N11Formalization.C450Source11GroupedC14.valid3
#print axioms N11Formalization.C450Source11GroupedC14.valid4
#print axioms N11Formalization.C450Source11GroupedC14.valid5
#print axioms N11Formalization.C450Source11GroupedC14.valid6
#print axioms N11Formalization.C450Source11GroupedC14.valid7
#print axioms N11Formalization.C450Source11GroupedC14.valid8
#print axioms N11Formalization.C450Source11GroupedC14.valid9
#print axioms N11Formalization.C450Source11GroupedC14.valid10
#print axioms N11Formalization.C450Source11GroupedC14.valid11
#print axioms N11Formalization.C450Source11GroupedC14.valid12
#print axioms N11Formalization.C450Source11GroupedC14.valid13
#print axioms N11Formalization.C450Source11GroupedC14.valid14
#print axioms N11Formalization.C450Source11GroupedC14.valid15
#print axioms N11Formalization.C450Source11GroupedC14.valid16
#print axioms N11Formalization.C450Source11GroupedC14.bound
#print axioms N11Formalization.C450Source11GroupedC14.endpoint_checks
