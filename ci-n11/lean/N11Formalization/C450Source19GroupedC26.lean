import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((1144894327:ℚ)/2000000000),((783597553:ℚ)/1250000000),((12480048943:ℚ)/21360000000),((927597553:ℚ)/1240000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7178526083:ℚ)/10000000000),((-33309587111841896002869343693342223:ℚ)/2436372864000000000000000000000000000),((-38981111790286579363275133:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((775161873:ℚ)/1250000000),((325354907:ℚ)/500000000),((8336456857:ℚ)/13825000000),((382954907:ℚ)/534000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3082043579:ℚ)/5000000000),((-1069507818641374712986881087044543314421324567777782153:ℚ)/49544641699218750000000000000000000000000000000000000000),((-6275577997210018613448213:ℚ)/18483200000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((1609903049:ℚ)/2500000000),((674536127:ℚ)/1000000000),((1564466131:ℚ)/2600000000),((789736127:ℚ)/1106000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2799413681:ℚ)/5000000000),((-2425801344509779337642730191192460242781113882310753:ℚ)/109850000000000000000000000000000000000000000000000000),((-25144014453389622338226973:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((834734357:ℚ)/1250000000),((107257407:ℚ)/156250000),((8872609213:ℚ)/14537500000),((11387037:ℚ)/16250000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4977317841:ℚ)/10000000000),((-366029998003482598711466907893164716687134229483923317:ℚ)/14401590701293945312500000000000000000000000000000000000),((-615698359704778477943213:ℚ)/1805000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((679698741:ℚ)/1000000000),((6983575111:ℚ)/10000000000),((7205288669:ℚ)/11820000000),((8135575111:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2319207667:ℚ)/5000000000),((-197500699736463263924588116588639690182474248906095781:ℚ)/7740940162500000000000000000000000000000000000000000000),((-2523830552772188958566113677:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6916088257:ℚ)/10000000000),((3551332509:ℚ)/5000000000),((73124794313:ℚ)/120100000000),((1375777503:ℚ)/1970000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4274842553:ℚ)/10000000000),((-831286217342983963928705360895786545841685160496625496897:ℚ)/32481067518750000000000000000000000000000000000000000000000),((-631424728892547127466073797:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((1407035591:ℚ)/2000000000),((3610872147:ℚ)/5000000000),((14839320319:ℚ)/24400000000),((4186872147:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((775927451:ℚ)/2000000000),((-2329216240622116704160466876787459195098514909854466093:ℚ)/90792400000000000000000000000000000000000000000000000000),((-631876399095298168524181733:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7154257029:ℚ)/10000000000),((7340813431:ℚ)/10000000000),((75268313261:ℚ)/123900000000),((8492813431:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3441884417:ℚ)/10000000000),((-25457975495825605550960328777183466441591217107919983309:ℚ)/990632770312500000000000000000000000000000000000000000000),((-2529250620280746622813494957:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7273325969:ℚ)/10000000000),((745987289:ℚ)/1000000000),((76339933721:ℚ)/125800000000),((861187289:ℚ)/1239000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((147130781:ℚ)/500000000),((-312614674162558676631841829587699985598295299588779123:ℚ)/12151278759765625000000000000000000000000000000000000000),((-25309340107117934530640077:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((7392385237:ℚ)/10000000000),((1539592897:ℚ)/2000000000),((77411467133:ℚ)/129600000000),((1769992897:ℚ)/2516000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2342777093:ℚ)/10000000000),((-11659906944194849327839267410854770768133175742285324093:ℚ)/503884800000000000000000000000000000000000000000000000000),((-41642469426723967:ℚ)/121600000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7630476469:ℚ)/10000000000),((4800841403:ℚ)/5000000000),((79554288221:ℚ)/160000000000),((5376841403:ℚ)/6480000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((49105775117162187910890735669303649:ℚ)/19200000000000000000000000000000000000),((-35200267:ℚ)/102400000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((1191774063:ℚ)/1250000000),((6703021287:ℚ)/5000000000),((12085966567:ℚ)/27600000000),((7279021287:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((600177791729708648790539:ℚ)/25392000000000000000000000),((-35200267:ℚ)/102400000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC26
#check @N11Formalization.C450Source19GroupedC26.bound
#print axioms N11Formalization.C450Source19GroupedC26.valid0
#print axioms N11Formalization.C450Source19GroupedC26.valid1
#print axioms N11Formalization.C450Source19GroupedC26.valid2
#print axioms N11Formalization.C450Source19GroupedC26.valid3
#print axioms N11Formalization.C450Source19GroupedC26.valid4
#print axioms N11Formalization.C450Source19GroupedC26.valid5
#print axioms N11Formalization.C450Source19GroupedC26.valid6
#print axioms N11Formalization.C450Source19GroupedC26.valid7
#print axioms N11Formalization.C450Source19GroupedC26.valid8
#print axioms N11Formalization.C450Source19GroupedC26.valid9
#print axioms N11Formalization.C450Source19GroupedC26.valid10
#print axioms N11Formalization.C450Source19GroupedC26.valid11
#print axioms N11Formalization.C450Source19GroupedC26.bound
#print axioms N11Formalization.C450Source19GroupedC26.endpoint_checks
