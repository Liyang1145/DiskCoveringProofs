import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((98128029:ℚ)/156250000),((6551276627:ℚ)/10000000000),((-5399276627:ℚ)/19840000000),((-73128029:ℚ)/402343750),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5982165797:ℚ)/10000000000),((645001232517740045605573341779938970350441323264271:ℚ)/18928872607648372650146484375000000000000000000000000),((3633899496361308905586659:ℚ)/77824000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6518056177:ℚ)/10000000000),((6789176621:ℚ)/10000000000),((-5637176621:ℚ)/20600000000),((-1639352059:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((540135573:ℚ)/1000000000),((3839657024310542071709811285779155111325289800770299237:ℚ)/113455948437500000000000000000000000000000000000000000000),((66735488803327023776853209:ℚ)/1478656000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6755892661:ℚ)/10000000000),((1381623221:ℚ)/2000000000),((-1151223221:ℚ)/4272000000),((-5155892661:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4757854197:ℚ)/10000000000),((1111540568616087823391867266359951287412785743389529350727:ℚ)/33488827080175781250000000000000000000000000000000000000000),((2573162281678087137836009:ℚ)/59146240000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((6874802063:ℚ)/10000000000),((6967583379:ℚ)/10000000000),((-5815583379:ℚ)/21740000000),((-5274802063:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4404046829:ℚ)/10000000000),((383549649964242842238586324809762352306113155954276348803:ℚ)/11662032555093383789062500000000000000000000000000000000000),((189379818492537720342319627:ℚ)/4435968000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((216695459:ℚ)/312500000),((878381133:ℚ)/1250000000),((-5692877:ℚ)/21250000),((-23813637:ℚ)/123437500),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4216816663:ℚ)/10000000000),((102584376749112793909312610892737966604479153169:ℚ)/3122412785887718200683593750000000000000000000000),((2932127597816177009847883:ℚ)/69312000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((6993705977:ℚ)/10000000000),((7086513201:ℚ)/10000000000),((-5934513201:ℚ)/22120000000),((-5393705977:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4021427077:ℚ)/10000000000),((153768012752180553719582046684784935604535344951479542841:ℚ)/4685046609667205810546875000000000000000000000000000000000),((9785994724021556821626913:ℚ)/233472000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((1763288991:ℚ)/2500000000),((7145975829:ℚ)/10000000000),((-5993975829:ℚ)/22310000000),((-1363288991:ℚ)/7031250000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3816621239:ℚ)/10000000000),((1862468386729166711369669666575429148451704778772116043:ℚ)/56801328901201486587524414062500000000000000000000000000),((9695421995032345301555833:ℚ)/233472000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7112604683:ℚ)/10000000000),((7205436987:ℚ)/10000000000),((-2017812329:ℚ)/7500000000),((-5512604683:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3600788693:ℚ)/10000000000),((35034848972966864472796453229030047966279425292109849:ℚ)/1069485269989013671875000000000000000000000000000000000),((182493519635942100930188443:ℚ)/4435968000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((1793013041:ℚ)/2500000000),((726489671:ℚ)/1000000000),((-611289671:ℚ)/2269000000),((-1393013041:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1685904159:ℚ)/5000000000),((169656060121225986249041464127621248370455157024516876349:ℚ)/5183613814843750000000000000000000000000000000000000000000),((602584679981947051352609:ℚ)/14786560000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((180787461:ℚ)/250000000),((1464871007:ℚ)/2000000000),((-112224637:ℚ)/416000000),((-140787461:ℚ)/720937500),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1563394167:ℚ)/5000000000),((116670588878961173044157685641984288401697520251:ℚ)/3567775408007204532623291015625000000000000000000),((2387448932566827490151601:ℚ)/59146240000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((7290943539:ℚ)/10000000000),((1845952999:ℚ)/2500000000),((-1557952999:ℚ)/5767500000),((-5690943539:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2861606671:ℚ)/10000000000),((11579591743268392355592687257642148077937404408555705731057:ℚ)/354394343977441406250000000000000000000000000000000000000000),((194455391002091783168571:ℚ)/4864000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7350387491:ℚ)/10000000000),((3751360979:ℚ)/5000000000),((-3175360979:ℚ)/11630000000),((-5750387491:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((642506109:ℚ)/2500000000),((57050621554745056114253501351584230254704602543261405619:ℚ)/1736634531054687500000000000000000000000000000000000000000),((14649888649438825934472409:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((1493854413:ℚ)/2000000000),((1548105381:ℚ)/2000000000),((-439235127:ℚ)/1576000000),((-1173854413:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((232181127:ℚ)/1250000000),((27825253101034079789779166929458998753145902788002557507:ℚ)/838411068750000000000000000000000000000000000000000000000),((3778833596022083:ℚ)/97280000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((3853514309:ℚ)/5000000000),((8216083057:ℚ)/10000000000),((-7064083057:ℚ)/24400000000),((-1017838103:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((676421627294217699571924506058826204318814849852692369:ℚ)/20011050000000000000000000000000000000000000000000000000),((19410903:ℚ)/512000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((4091248261:ℚ)/5000000000),((2023555729:ℚ)/2000000000),((-1793155729:ℚ)/5184000000),((-3291248261:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((150728788747801138797226257445031576975335394128515557821:ℚ)/4050000000000000000000000000000000000000000000000000000000),((19410903:ℚ)/512000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10083923151:ℚ)/10000000000),((434992751:ℚ)/312500000),((-398992751:ℚ)/1000000000),((-8483923151:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((32975320488685148592641330055995285310598106456727277973:ℚ)/788421600000000000000000000000000000000000000000000000000),((19410903:ℚ)/512000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC12
#check @N11Formalization.C450Source11GroupedC12.bound
#print axioms N11Formalization.C450Source11GroupedC12.valid0
#print axioms N11Formalization.C450Source11GroupedC12.valid1
#print axioms N11Formalization.C450Source11GroupedC12.valid2
#print axioms N11Formalization.C450Source11GroupedC12.valid3
#print axioms N11Formalization.C450Source11GroupedC12.valid4
#print axioms N11Formalization.C450Source11GroupedC12.valid5
#print axioms N11Formalization.C450Source11GroupedC12.valid6
#print axioms N11Formalization.C450Source11GroupedC12.valid7
#print axioms N11Formalization.C450Source11GroupedC12.valid8
#print axioms N11Formalization.C450Source11GroupedC12.valid9
#print axioms N11Formalization.C450Source11GroupedC12.valid10
#print axioms N11Formalization.C450Source11GroupedC12.valid11
#print axioms N11Formalization.C450Source11GroupedC12.valid12
#print axioms N11Formalization.C450Source11GroupedC12.valid13
#print axioms N11Formalization.C450Source11GroupedC12.valid14
#print axioms N11Formalization.C450Source11GroupedC12.valid15
#print axioms N11Formalization.C450Source11GroupedC12.bound
#print axioms N11Formalization.C450Source11GroupedC12.endpoint_checks
