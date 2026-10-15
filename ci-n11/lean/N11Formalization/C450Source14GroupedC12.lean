import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((6302556103:ℚ)/10000000000),((1316204211:ℚ)/2000000000),((-1009004211:ℚ)/3968000000),((-4222556103:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2964858293:ℚ)/5000000000),((156136144891517380311105387302467302568407526580263583103:ℚ)/3308060253906250000000000000000000000000000000000000000000),((10702087609034272779320511:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6540701381:ℚ)/10000000000),((6819198227:ℚ)/10000000000),((-5283198227:ℚ)/20600000000),((-4460701381:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5343131657:ℚ)/10000000000),((143548869069431882380870466689099512547523438487222171997:ℚ)/3063310607812500000000000000000000000000000000000000000000),((10053167505562879522079319:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((1355760113:ℚ)/2000000000),((3469134493:ℚ)/5000000000),((-2701134493:ℚ)/10680000000),((-939760113:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4691621131:ℚ)/10000000000),((4103843399563038585618436700563057145132693498433229687:ℚ)/89303538880468750000000000000000000000000000000000000000),((376164392685166255403151:ℚ)/9241600000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((6897834391:ℚ)/10000000000),((349890009:ℚ)/500000000),((-273090009:ℚ)/1087000000),((-94467341:ℚ)/537500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((216620633:ℚ)/500000000),((12009047742284625174745411943842033441440966668512293:ℚ)/263745449829101562500000000000000000000000000000000000),((9079525283164000656815199:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((3478673801:ℚ)/5000000000),((7057328681:ℚ)/10000000000),((-5521328681:ℚ)/21930000000),((-2438673801:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1035488233:ℚ)/2500000000),((8579341239916689439920682168180761454971673717883370421:ℚ)/188630901469421386718750000000000000000000000000000000000),((2229304612040017973978079:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7016858431:ℚ)/10000000000),((7116854557:ℚ)/10000000000),((-5580854557:ℚ)/22120000000),((-4936858431:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((123214567:ℚ)/312500000),((212858840885865629298720163917306629528765054976875660073:ℚ)/4685046609667205810546875000000000000000000000000000000000),((8754901669290866040532719:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((3538183469:ℚ)/5000000000),((57411023:ℚ)/80000000),((-45123023:ℚ)/178480000),((-277575941:ℚ)/1562500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1866884227:ℚ)/5000000000),((28291373407545613380386869552325063519764552398909127:ℚ)/623334199190139770507812500000000000000000000000000000),((2148143696213649412536519:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((222996037:ℚ)/312500000),((72358987:ℚ)/100000000),((-56998987:ℚ)/225000000),((-157996037:ℚ)/886328125),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1756434179:ℚ)/5000000000),((5919586010226879572705043043678267525343023873361:ℚ)/130552401121705770492553710937500000000000000000000),((8232653935893457401051:ℚ)/225625000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((899422153:ℚ)/1250000000),((1459083419:ℚ)/2000000000),((-1151883419:ℚ)/4538000000),((-639422153:ℚ)/3575000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1638887983:ℚ)/5000000000),((29352162768430429584931194092107712553169257916329315107:ℚ)/647951726855468750000000000000000000000000000000000000000),((129185782149981823545711:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3627439557:ℚ)/5000000000),((7354933119:ℚ)/10000000000),((-5818933119:ℚ)/22880000000),((-2587439557:ℚ)/14418750000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3025179477:ℚ)/10000000000),((14209726418049095889234733836294327593838349613100887:ℚ)/313964235904633998870849609375000000000000000000000000),((2026382978900968150146071:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((7314378907:ℚ)/10000000000),((463402927:ℚ)/625000000),((-367402927:ℚ)/1441875000),((-5234378907:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1375127421:ℚ)/5000000000),((5341900170326486926184501498466147762527550764871980660677:ℚ)/118131447992480468750000000000000000000000000000000000000000),((7943163061512645669499671:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1474775331:ℚ)/2000000000),((941683443:ℚ)/1250000000),((-749683443:ℚ)/2907500000),((-1058775331:ℚ)/5910000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2445477237:ℚ)/10000000000),((631583447335571424332099278396296601993926610563467461:ℚ)/13893076248437500000000000000000000000000000000000000000),((311231334205539573658919:ℚ)/9241600000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((3746433107:ℚ)/5000000000),((7771483591:ℚ)/10000000000),((-6235483591:ℚ)/23640000000),((-2706433107:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((840529437:ℚ)/5000000000),((200511153624829147059718713238226133921556906410518473529:ℚ)/4366724316406250000000000000000000000000000000000000000000),((1863997712951459786924871:ℚ)/57760000000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((7730822883:ℚ)/10000000000),((8247424631:ℚ)/10000000000),((-6711424631:ℚ)/24400000000),((-5650822883:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((202085556274592247784793441840398041367608517903194764171:ℚ)/4322386800000000000000000000000000000000000000000000000000),((39687:ℚ)/1280000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((1025831959:ℚ)/1250000000),((79299163:ℚ)/78125000),((-67299163:ℚ)/202500000),((-765831959:ℚ)/5000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1084535106826622431485440943238294115357287849002686107:ℚ)/21093750000000000000000000000000000000000000000000000000),((39687:ℚ)/1280000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10109194159:ℚ)/10000000000),((872103551:ℚ)/625000000),((-776103551:ℚ)/2000000000),((-2676398053:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1690352565691127129522739389100218152443047599706140969:ℚ)/29200800000000000000000000000000000000000000000000000000),((39687:ℚ)/1280000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC12
#check @N11Formalization.C450Source14GroupedC12.bound
#print axioms N11Formalization.C450Source14GroupedC12.valid0
#print axioms N11Formalization.C450Source14GroupedC12.valid1
#print axioms N11Formalization.C450Source14GroupedC12.valid2
#print axioms N11Formalization.C450Source14GroupedC12.valid3
#print axioms N11Formalization.C450Source14GroupedC12.valid4
#print axioms N11Formalization.C450Source14GroupedC12.valid5
#print axioms N11Formalization.C450Source14GroupedC12.valid6
#print axioms N11Formalization.C450Source14GroupedC12.valid7
#print axioms N11Formalization.C450Source14GroupedC12.valid8
#print axioms N11Formalization.C450Source14GroupedC12.valid9
#print axioms N11Formalization.C450Source14GroupedC12.valid10
#print axioms N11Formalization.C450Source14GroupedC12.valid11
#print axioms N11Formalization.C450Source14GroupedC12.valid12
#print axioms N11Formalization.C450Source14GroupedC12.valid13
#print axioms N11Formalization.C450Source14GroupedC12.valid14
#print axioms N11Formalization.C450Source14GroupedC12.valid15
#print axioms N11Formalization.C450Source14GroupedC12.bound
#print axioms N11Formalization.C450Source14GroupedC12.endpoint_checks
