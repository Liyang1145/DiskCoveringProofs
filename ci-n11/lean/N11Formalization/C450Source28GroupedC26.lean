import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((9:ℚ)/16),((5:ℚ)/8),((5467411983:ℚ)/10000000000),((5794814361:ℚ)/10000000000),((65846707847:ℚ)/103000000000),((242671431:ℚ)/320000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7678635137:ℚ)/10000000000),((-59213439358385159287445745926914581711:ℚ)/273181750000000000000000000000000000000),((-6298760452503704155474172769:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5707055407:ℚ)/10000000000),((1206876883:ℚ)/2000000000),((68003498663:ℚ)/106800000000),((1552476883:ℚ)/2060000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7213296063:ℚ)/10000000000),((-6433794595448582232982574822056815353153886132936339173:ℚ)/29740879687500000000000000000000000000000000000000000000),((-250521789740498429419436121:ℚ)/591462400000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((5946544379:ℚ)/10000000000),((6154114489:ℚ)/10000000000),((70158899411:ℚ)/108700000000),((7882114489:ℚ)/10680000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1344443523:ℚ)/2000000000),((-5423904772058860382403055726387471437258504728096612252963:ℚ)/24081853181250000000000000000000000000000000000000000000000),((-6264775987983417554781591969:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6066236091:ℚ)/10000000000),((3136905243:ℚ)/5000000000),((71236124819:ℚ)/110600000000),((4000905243:ℚ)/5435000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1616283663:ℚ)/2500000000),((-356291780558312086075656412355567429705840903671171408043:ℚ)/1585428534375000000000000000000000000000000000000000000000),((-1561242648723996421443097161:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((3092947537:ℚ)/5000000000),((79918427:ℚ)/125000000),((36156527833:ℚ)/56250000000),((101518427:ℚ)/138250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3099525767:ℚ)/5000000000),((-83140479700866418152746178512114509536115129091993409041:ℚ)/370788574218750000000000000000000000000000000000000000000),((-51187414734131852494899:ℚ)/121600000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((1576380753:ℚ)/2500000000),((1302621429:ℚ)/2000000000),((18347426777:ℚ)/28600000000),((549407143:ℚ)/750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5922727217:ℚ)/10000000000),((-2973639632393246201862355345979534584207858326283692777:ℚ)/13291850000000000000000000000000000000000000000000000000),((-248121337705458818720847849:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((257004859:ℚ)/400000000),((6632710967:ℚ)/10000000000),((2978643731:ℚ)/4652000000),((8360710967:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5634626561:ℚ)/10000000000),((-105334189749080288049138811277162183204180476124422163:ℚ)/471911324100000000000000000000000000000000000000000000),((-6180902348626298388163382721:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6544691927:ℚ)/10000000000),((1688071763:ℚ)/2500000000),((75542227343:ℚ)/118200000000),((2120071763:ℚ)/2907500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5332811969:ℚ)/10000000000),((-1723843233828150054556430170520806573814955683052672392519:ℚ)/7740940162500000000000000000000000000000000000000000000000),((-384874790560211959017962841:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((3332117869:ℚ)/5000000000),((1374367347:ℚ)/2000000000),((38309060821:ℚ)/60050000000),((573322449:ℚ)/788000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5014777699:ℚ)/10000000000),((-902045110847388981508623335615161054242737952405149454493:ℚ)/4060133439843750000000000000000000000000000000000000000000),((-245372664938134363429362201:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((6783754187:ℚ)/10000000000),((3495680633:ℚ)/5000000000),((77693787683:ℚ)/122000000000),((4359680633:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4677184821:ℚ)/10000000000),((-2515474551127811399182582222089866876301419669765050471337:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-1527465633400758465196601121:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1725812119:ℚ)/2500000000),((3615169743:ℚ)/5000000000),((19692309071:ℚ)/31450000000),((4479169743:ℚ)/6100000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((431541251:ℚ)/1000000000),((-10364825624021748478339953763471567453120885445343179981:ℚ)/48605115039062500000000000000000000000000000000000000000),((-1509480739095199711608430161:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((3571084501:ℚ)/5000000000),((7469230257:ℚ)/10000000000),((40459760509:ℚ)/64800000000),((9197230257:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3488714873:ℚ)/10000000000),((-13382675224477637661985865597306121661148091544591882853:ℚ)/62985600000000000000000000000000000000000000000000000000),((-5983607496902823630890830161:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7381005521:ℚ)/10000000000),((1172245333:ℚ)/1250000000),((83069049689:ℚ)/160000000000),((1388245333:ℚ)/1620000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2406429763:ℚ)/10000000000),((-641579429896859150631144079224998210498534339364165881753:ℚ)/4800000000000000000000000000000000000000000000000000000000),((-12276495802697211:ℚ)/30400000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((580587367:ℚ)/625000000),((13188185001:ℚ)/10000000000),((6265286303:ℚ)/13800000000),((14916185001:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-50560255385478285184823:ℚ)/661250000000000000000000),((-416153043:ℚ)/1024000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC26
#check @N11Formalization.C450Source28GroupedC26.bound
#print axioms N11Formalization.C450Source28GroupedC26.valid0
#print axioms N11Formalization.C450Source28GroupedC26.valid1
#print axioms N11Formalization.C450Source28GroupedC26.valid2
#print axioms N11Formalization.C450Source28GroupedC26.valid3
#print axioms N11Formalization.C450Source28GroupedC26.valid4
#print axioms N11Formalization.C450Source28GroupedC26.valid5
#print axioms N11Formalization.C450Source28GroupedC26.valid6
#print axioms N11Formalization.C450Source28GroupedC26.valid7
#print axioms N11Formalization.C450Source28GroupedC26.valid8
#print axioms N11Formalization.C450Source28GroupedC26.valid9
#print axioms N11Formalization.C450Source28GroupedC26.valid10
#print axioms N11Formalization.C450Source28GroupedC26.valid11
#print axioms N11Formalization.C450Source28GroupedC26.valid12
#print axioms N11Formalization.C450Source28GroupedC26.valid13
#print axioms N11Formalization.C450Source28GroupedC26.bound
#print axioms N11Formalization.C450Source28GroupedC26.endpoint_checks
