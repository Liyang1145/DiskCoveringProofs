import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6351568109:ℚ)/10000000000),((6633013801:ℚ)/10000000000),((-39391096607:ℚ)/99200000000),((-15214704327:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5813307151:ℚ)/10000000000),((238844921189771230020726881733273869520752081466175489337:ℚ)/5292896406250000000000000000000000000000000000000000000000),((385704725997525974393968287:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6589564671:ℚ)/10000000000),((858878791:ℚ)/1250000000),((-5132151537:ℚ)/12875000000),((-5309564671:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5215499807:ℚ)/10000000000),((8154709095340141097814019613416203212134941608737413337:ℚ)/181529517500000000000000000000000000000000000000000000000),((5923698368007447372708247:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1365505159:ℚ)/2000000000),((6990025007:ℚ)/10000000000),((-13963391683:ℚ)/35600000000),((-3328515477:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4547777941:ℚ)/10000000000),((6260264495896191349326474677483922854785720049325752093:ℚ)/142885662208750000000000000000000000000000000000000000000),((19599653397419715825248277:ℚ)/194560000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6946494233:ℚ)/10000000000),((7049519157:ℚ)/10000000000),((-42306634099:ℚ)/108700000000),((-5666494233:ℚ)/18275000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((167091807:ℚ)/400000000),((89756843002643267366800910639577033257060888562758522671:ℚ)/2073250232016601562500000000000000000000000000000000000000),((369033044846772758155649463:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((1401195121:ℚ)/2000000000),((3554505627:ℚ)/5000000000),((-21361539389:ℚ)/54825000000),((-490797909:ℚ)/1580000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((248748537:ℚ)/625000000),((7310308312689119314781394947013095176909408241868077:ℚ)/168942894843750000000000000000000000000000000000000000),((91847481679861835537915223:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3532727573:ℚ)/5000000000),((7168501351:ℚ)/10000000000),((-43139509457:ℚ)/110600000000),((-8678182719:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3772934419:ℚ)/10000000000),((40525339699512746735852381461265603770677784420502655327:ℚ)/937009321933441162109375000000000000000000000000000000000),((365747475388462497520279487:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((7124932901:ℚ)/10000000000),((1439649133:ℚ)/2000000000),((-8669543931:ℚ)/22310000000),((-17534798703:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3554465723:ℚ)/10000000000),((843027878546152875458948449459278873592106567031031172737:ℚ)/19603086008405371093750000000000000000000000000000000000000),((766459623709442164559997:ℚ)/7782400000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7154671123:ℚ)/10000000000),((3613994749:ℚ)/5000000000),((-21777963243:ℚ)/56012500000),((-5874671123:ℚ)/18750000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((344026933:ℚ)/1000000000),((18603770754630441467220096630873898944649910581823033729:ℚ)/432683229446411132812500000000000000000000000000000000000),((90811881001735941363938087:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((1796102229:ℚ)/2500000000),((907216607:ℚ)/1250000000),((-5470516249:ℚ)/14062500000),((-4428306687:ℚ)/14121875000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3322312673:ℚ)/10000000000),((1361994763800566279996756411365602788651703214485531007:ℚ)/31683241776695251464843750000000000000000000000000000000),((5662920197222114199106063:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1442829257:ℚ)/2000000000),((1457495149:ℚ)/2000000000),((-8794466043:ℚ)/22595000000),((-3560487771:ℚ)/11345000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3200179411:ℚ)/10000000000),((886274110002794163393288845903246520871850830816951909:ℚ)/20620816789676171875000000000000000000000000000000000000),((761276688344729522830973:ℚ)/7782400000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((1448776647:ℚ)/2000000000),((367348007:ℚ)/500000000),((-2219436049:ℚ)/5672500000),((-3578329941:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3073371073:ℚ)/10000000000),((183403123164716715792253089895420517518817592126169851961:ℚ)/4246416437120000000000000000000000000000000000000000000000),((902060272864046173631263:ℚ)/9241600000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7303355901:ℚ)/10000000000),((7406442727:ℚ)/10000000000),((-44805099089:ℚ)/114400000000),((-6023355901:ℚ)/19225000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2803166517:ℚ)/10000000000),((584159090321584229330879859743920239705395830495019:ℚ)/13531118584442138671875000000000000000000000000000000),((359184312058644173512121023:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3681413477:ℚ)/5000000000),((233310111:ℚ)/312500000),((-1413170777:ℚ)/3604687500),((-9124240431:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((313102703:ℚ)/1250000000),((3058677015430963482958286023045566796659362228706017951597:ℚ)/70878868795488281250000000000000000000000000000000000000000),((681963301631786584921:ℚ)/7050781250000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((3711148217:ℚ)/5000000000),((3792440043:ℚ)/5000000000),((-23027080301:ℚ)/58150000000),((-3071148217:ℚ)/9850000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2166736749:ℚ)/10000000000),((15127324835887955590054236099214729875366411772792984571:ℚ)/347326906210937500000000000000000000000000000000000000000),((88996241292267568577103863:ℚ)/924160000000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((7541230827:ℚ)/10000000000),((7822773807:ℚ)/10000000000),((-47719416649:ℚ)/118200000000),((-18783692481:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((622204651:ℚ)/5000000000),((7430164323222478787943979911481682030407185187993138660519:ℚ)/167682213750000000000000000000000000000000000000000000000000),((92782324039144709:ℚ)/972800000000000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((1555816469:ℚ)/2000000000),((8298491827:ℚ)/10000000000),((-51049442789:ℚ)/122000000000),((-1299816469:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((93596983803806907655319075418166836191152684388060747:ℚ)/2049131520000000000000000000000000000000000000000000000),((4859791:ℚ)/51200000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((8254723417:ℚ)/10000000000),((510034033:ℚ)/500000000),((-1072746077:ℚ)/2160000000),((-20924170251:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((910047175607405565358859710403586350631406285664467187233:ℚ)/17280000000000000000000000000000000000000000000000000000000),((4859791:ℚ)/51200000)⟩
theorem valid16 : Valid source13 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((2031335557:ℚ)/2000000000),((14003248351:ℚ)/10000000000),((-90982738457:ℚ)/160000000000),((-1775335557:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((7510122926822550150196041386832831690054277706339157:ℚ)/124590080000000000000000000000000000000000000000000000),((4859791:ℚ)/51200000)⟩
theorem valid17 : Valid source13 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source13 nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source13 nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source13 nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC10
#check @N11Formalization.C450Source13GroupedC10.bound
#print axioms N11Formalization.C450Source13GroupedC10.valid0
#print axioms N11Formalization.C450Source13GroupedC10.valid1
#print axioms N11Formalization.C450Source13GroupedC10.valid2
#print axioms N11Formalization.C450Source13GroupedC10.valid3
#print axioms N11Formalization.C450Source13GroupedC10.valid4
#print axioms N11Formalization.C450Source13GroupedC10.valid5
#print axioms N11Formalization.C450Source13GroupedC10.valid6
#print axioms N11Formalization.C450Source13GroupedC10.valid7
#print axioms N11Formalization.C450Source13GroupedC10.valid8
#print axioms N11Formalization.C450Source13GroupedC10.valid9
#print axioms N11Formalization.C450Source13GroupedC10.valid10
#print axioms N11Formalization.C450Source13GroupedC10.valid11
#print axioms N11Formalization.C450Source13GroupedC10.valid12
#print axioms N11Formalization.C450Source13GroupedC10.valid13
#print axioms N11Formalization.C450Source13GroupedC10.valid14
#print axioms N11Formalization.C450Source13GroupedC10.valid15
#print axioms N11Formalization.C450Source13GroupedC10.valid16
#print axioms N11Formalization.C450Source13GroupedC10.valid17
#print axioms N11Formalization.C450Source13GroupedC10.bound
#print axioms N11Formalization.C450Source13GroupedC10.endpoint_checks
