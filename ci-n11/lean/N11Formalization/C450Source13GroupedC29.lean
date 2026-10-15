import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((5803682263:ℚ)/10000000000),((1267730483:ℚ)/2000000000),((19171046789:ℚ)/26700000000),((18016496279:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1754650841:ℚ)/2500000000),((-17857878527852093267240580195116197963:ℚ)/475854075000000000000000000000000000000),((-876574854657971270020809197:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((25116529:ℚ)/40000000),((6576370703:ℚ)/10000000000),((11769941:ℚ)/15800000),((93172819139:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2992322841:ℚ)/5000000000),((-642323527689130146795870862159670159414705743:ℚ)/14791170000000000000000000000000000000000000000),((-13970625358999662891133:ℚ)/59146240000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((6516834023:ℚ)/10000000000),((681407447:ℚ)/1000000000),((21310502069:ℚ)/28600000000),((9626296811:ℚ)/11060000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2702240987:ℚ)/5000000000),((-1275228539681126072716794362817842656767036440114447181:ℚ)/29242070000000000000000000000000000000000000000000000000),((-869683215647596370772492877:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((54036179:ℚ)/80000000),((3466460677:ℚ)/5000000000),((176188537:ℚ)/232600000),((48903988801:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4761789077:ℚ)/10000000000),((-545691722822481429805173397742960697731554963859:ℚ)/11797783102500000000000000000000000000000000000000),((-55551062503849356616933:ℚ)/236584960000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((687336193:ℚ)/1000000000),((6992343617:ℚ)/10000000000),((2238008579:ℚ)/2931250000),((98580467021:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((4408489697:ℚ)/10000000000),((-160368011586103571369214266880854069390699042621839:ℚ)/3373120193481445312500000000000000000000000000000000),((-8671375378331372443006237:ℚ)/36966400000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3466390309:ℚ)/5000000000),((11018383:ℚ)/15625000),((11279170927:ℚ)/14775000000),((22176997:ℚ)/26171875),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((844310591:ℚ)/2000000000),((-15971948076169563422450100482826403697027009903959909:ℚ)/335978305664062500000000000000000000000000000000000000),((-216567236531700775281007253:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6992198603:ℚ)/10000000000),((177779647:ℚ)/250000000),((22736595809:ℚ)/29787500000),((2503135411:ℚ)/2955000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((805298319:ℚ)/2000000000),((-4711264901392761170513330129568433324164127320037627267:ℚ)/99113641750488281250000000000000000000000000000000000000),((-865400548974318415278804917:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3525807951:ℚ)/5000000000),((1792651479:ℚ)/2500000000),((11457423853:ℚ)/15012500000),((25224469227:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3822058083:ℚ)/10000000000),((-12563406388101864002617751874782311059424143646784997:ℚ)/264331604156494140625000000000000000000000000000000000),((-216133086522711319231065213:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((7111032531:ℚ)/10000000000),((7230025243:ℚ)/10000000000),((23093097593:ℚ)/30262500000),((101670328159:ℚ)/120100000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1803327541:ℚ)/5000000000),((-182932689639392118098158845116126276597286507175766033:ℚ)/3849301340332031250000000000000000000000000000000000000),((-863664337251292443338443493:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((1434089701:ℚ)/2000000000),((182236097:ℚ)/250000000),((4654269103:ℚ)/6100000000),((2561069261:ℚ)/3026250000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1689090349:ℚ)/5000000000),((-13482081812082738310498027767382848016891286001665167:ℚ)/283726250000000000000000000000000000000000000000000000),((-34511860886819487369928213:ℚ)/147865600000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((7229863841:ℚ)/10000000000),((7348861841:ℚ)/10000000000),((23449591523:ℚ)/30737500000),((103215203933:ℚ)/122000000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((195860797:ℚ)/625000000),((-431179522526711749840717561751380701098145293690296547:ℚ)/9075188341674804687500000000000000000000000000000000000),((-861928900639077522695858653:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((7289278553:ℚ)/10000000000),((7408279143:ℚ)/10000000000),((23627835659:ℚ)/30975000000),((103987628859:ℚ)/122950000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((2869357693:ℚ)/10000000000),((-196085754959825247943644354030369898741238347852642291:ℚ)/4127636542968750000000000000000000000000000000000000000),((-861061472401854288254093517:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((459293291:ℚ)/625000000),((7527111829:ℚ)/10000000000),((1487879873:ℚ)/1965625000),((105532453777:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((644695811:ℚ)/2500000000),((-429480977275706370771376310948974164171132171863:ℚ)/9270689971745014190673828125000000000000000000000),((-3356657765411511507113603:ℚ)/14440000000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((466719943:ℚ)/625000000),((7764769919:ℚ)/10000000000),((1510159829:ℚ)/2025000000),((108622008947:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1869897311:ℚ)/10000000000),((-16959877936005170518305150566311118464028624669783:ℚ)/384433593750000000000000000000000000000000000000000),((-3352572536423859525476237:ℚ)/14440000000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7705165221:ℚ)/10000000000),((1933152821:ℚ)/2000000000),((24875495663:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-331358355554770551733577562815649340305958510309959469:ℚ)/15000000000000000000000000000000000000000000000000000000),((-11887957:ℚ)/51200000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((9606084231:ℚ)/10000000000),((13466930821:ℚ)/10000000000),((30578252693:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-74903817526979492173443818953739279:ℚ)/8409830400000000000000000000000000000),((-11887957:ℚ)/51200000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC29
#check @N11Formalization.C450Source13GroupedC29.bound
#print axioms N11Formalization.C450Source13GroupedC29.valid0
#print axioms N11Formalization.C450Source13GroupedC29.valid1
#print axioms N11Formalization.C450Source13GroupedC29.valid2
#print axioms N11Formalization.C450Source13GroupedC29.valid3
#print axioms N11Formalization.C450Source13GroupedC29.valid4
#print axioms N11Formalization.C450Source13GroupedC29.valid5
#print axioms N11Formalization.C450Source13GroupedC29.valid6
#print axioms N11Formalization.C450Source13GroupedC29.valid7
#print axioms N11Formalization.C450Source13GroupedC29.valid8
#print axioms N11Formalization.C450Source13GroupedC29.valid9
#print axioms N11Formalization.C450Source13GroupedC29.valid10
#print axioms N11Formalization.C450Source13GroupedC29.valid11
#print axioms N11Formalization.C450Source13GroupedC29.valid12
#print axioms N11Formalization.C450Source13GroupedC29.valid13
#print axioms N11Formalization.C450Source13GroupedC29.valid14
#print axioms N11Formalization.C450Source13GroupedC29.valid15
#print axioms N11Formalization.C450Source13GroupedC29.bound
#print axioms N11Formalization.C450Source13GroupedC29.endpoint_checks
