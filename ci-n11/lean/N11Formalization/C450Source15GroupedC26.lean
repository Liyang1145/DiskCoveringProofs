import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((2917284753:ℚ)/5000000000),((3184319819:ℚ)/5000000000),((30415562777:ℚ)/53400000000),((3632319819:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3477709893:ℚ)/5000000000),((-148449262771908378333989507747288207:ℚ)/12689442000000000000000000000000000000),((-939940605222827515858433643:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6310670009:ℚ)/10000000000),((3303308397:ℚ)/5000000000),((65116030081:ℚ)/110600000000),((3751308397:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2955292399:ℚ)/5000000000),((-140750942656097105885656504612833766204167845821174784471:ℚ)/8455618850000000000000000000000000000000000000000000000000),((-945868975379705462579764667:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((1637165841:ℚ)/2500000000),((6844562161:ℚ)/10000000000),((16814492569:ℚ)/28600000000),((7740562161:ℚ)/11060000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1064504751:ℚ)/2000000000),((-2486207588531175243056728589271278617935219803772126151:ℚ)/146210350000000000000000000000000000000000000000000000000),((-3794066699365990646741586723:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6786623849:ℚ)/10000000000),((6963523901:ℚ)/10000000000),((69399614641:ℚ)/116300000000),((7859523901:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2334401439:ℚ)/5000000000),((-46952497225005160867161310105834751245365658021355393591:ℚ)/2457871479687500000000000000000000000000000000000000000000),((-3805843271754320223368539163:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((863199097:ℚ)/1250000000),((221327463:ℚ)/312500000),((8808791873:ℚ)/14775000000),((249327463:ℚ)/363437500),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2154015971:ℚ)/5000000000),((-32236962358330894922695433070493189751468417784350461:ℚ)/1679891528320312500000000000000000000000000000000000000),((-3721761132537394561942547:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((1404910929:ℚ)/2000000000),((7141953817:ℚ)/10000000000),((14308198361:ℚ)/23830000000),((2679317939:ℚ)/3940000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1958210499:ℚ)/5000000000),((-1705399452026314902524360682689280771412398429764335591:ℚ)/84576974293750000000000000000000000000000000000000000000),((-3816951867035908831323313107:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7084033039:ℚ)/10000000000),((7201427231:ℚ)/10000000000),((72076297351:ℚ)/120100000000),((8097427231:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1853008259:ℚ)/5000000000),((-13660865400198931832355186953319456975789027786775439881:ℚ)/676688906640625000000000000000000000000000000000000000000),((-3819558160992758539517333443:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((7143509793:ℚ)/10000000000),((3630449549:ℚ)/5000000000),((72611588137:ℚ)/121050000000),((4078449549:ℚ)/6005000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3483550279:ℚ)/10000000000),((-24893148121194749729913986872607868078665483441612360047:ℚ)/1231776428906250000000000000000000000000000000000000000000),((-955539747521038968078531963:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((7202984947:ℚ)/10000000000),((1830092363:ℚ)/2500000000),((73146864523:ℚ)/122000000000),((2054092363:ℚ)/3026250000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((649307833:ℚ)/2000000000),((-229567988003678456225145804329317765160484977264855039997:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-239047147283843219799088747:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((907807317:ℚ)/1250000000),((7439305763:ℚ)/10000000000),((9210265853:ℚ)/15487500000),((8335305763:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2991523303:ℚ)/10000000000),((-37497926918570042912446176467018639315122433405462449:ℚ)/1934829629516601562500000000000000000000000000000000000),((-3826672535997174821739337947:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((461337573:ℚ)/625000000),((7558236433:ℚ)/10000000000),((4672038157:ℚ)/7862500000),((2818078811:ℚ)/4130000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2404244447:ℚ)/10000000000),((-57618915677293207658291645019362023905543691653267:ℚ)/2966620790958404541015625000000000000000000000000000),((-3831825223603459871151835107:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((468771123:ℚ)/625000000),((7796081847:ℚ)/10000000000),((4738940107:ℚ)/8100000000),((234921131:ℚ)/340000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1621245587:ℚ)/10000000000),((-731859754296783857324042640661384286106833779308397:ℚ)/41006250000000000000000000000000000000000000000000000),((-789032612284419:ℚ)/3040000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7738195099:ℚ)/10000000000),((484912677:ℚ)/500000000),((77963755891:ℚ)/160000000000),((529712677:ℚ)/648000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-56653068019487216615863250749514941:ℚ)/32000000000000000000000000000000000000),((-266157289:ℚ)/1024000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((2410110107:ℚ)/2500000000),((13500801139:ℚ)/10000000000),((23770990963:ℚ)/55200000000),((14396801139:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((16869371081018123351717921:ℚ)/1523520000000000000000000000),((-266157289:ℚ)/1024000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC26
#check @N11Formalization.C450Source15GroupedC26.bound
#print axioms N11Formalization.C450Source15GroupedC26.valid0
#print axioms N11Formalization.C450Source15GroupedC26.valid1
#print axioms N11Formalization.C450Source15GroupedC26.valid2
#print axioms N11Formalization.C450Source15GroupedC26.valid3
#print axioms N11Formalization.C450Source15GroupedC26.valid4
#print axioms N11Formalization.C450Source15GroupedC26.valid5
#print axioms N11Formalization.C450Source15GroupedC26.valid6
#print axioms N11Formalization.C450Source15GroupedC26.valid7
#print axioms N11Formalization.C450Source15GroupedC26.valid8
#print axioms N11Formalization.C450Source15GroupedC26.valid9
#print axioms N11Formalization.C450Source15GroupedC26.valid10
#print axioms N11Formalization.C450Source15GroupedC26.valid11
#print axioms N11Formalization.C450Source15GroupedC26.valid12
#print axioms N11Formalization.C450Source15GroupedC26.valid13
#print axioms N11Formalization.C450Source15GroupedC26.bound
#print axioms N11Formalization.C450Source15GroupedC26.endpoint_checks
