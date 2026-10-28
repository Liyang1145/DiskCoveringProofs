import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((3296491507:ℚ)/5000000000),((10796723:ℚ)/15625000),((-75170507:ℚ)/155000000),((-2376491507:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5206465009:ℚ)/10000000000),((17601433416471357674152422969244340015016803353642870571:ℚ)/77532662200927734375000000000000000000000000000000000000),((77844384125708409010787:ℚ)/409600000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((26688399:ℚ)/39062500),((7029475149:ℚ)/10000000000),((-49185276341:ℚ)/103000000000),((-156007192:ℚ)/409765625),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4533665929:ℚ)/10000000000),((609714211488252544331263108424462476147900832887717:ℚ)/2768240562803111970424652099609375000000000000000000),((1641042508571766556143:ℚ)/9025000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6951805743:ℚ)/10000000000),((354462509:ℚ)/500000000),((-2486162581:ℚ)/5245000000),((-5111805743:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4160034427:ℚ)/10000000000),((1648258933580788765036127220657830328675755750341385344947:ℚ)/7593257643155670166015625000000000000000000000000000000000),((105087952954725677117887107:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((3505791157:ℚ)/5000000000),((7149018023:ℚ)/10000000000),((-50261162207:ℚ)/105850000000),((-2585791157:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((792179767:ℚ)/2000000000),((106757511786323120344824326876245906124444326108766608069:ℚ)/491886267956542968750000000000000000000000000000000000000),((25962719672001761704000907:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((707135167:ℚ)/1000000000),((7208778871:ℚ)/10000000000),((-50799009839:ℚ)/106800000000),((-523135167:ℚ)/1346875000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((468977281:ℚ)/1250000000),((1728127037239074901646010357224485350561913192157429:ℚ)/7963485493138432502746582031250000000000000000000000),((1026088881079344932168227:ℚ)/5914624000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7131114003:ℚ)/10000000000),((726853291:ℚ)/1000000000),((-5133679619:ℚ)/10775000000),((-5291114003:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((706204301:ℚ)/2000000000),((733093349416407058620843567204736097852468498311823361713:ℚ)/3378671458697509765625000000000000000000000000000000000000),((101361979034762306669031387:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3595434751:ℚ)/5000000000),((7328280319:ℚ)/10000000000),((-51874522871:ℚ)/108700000000),((-2675434751:ℚ)/6853125000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3296149701:ℚ)/10000000000),((19766073254297584479254258011614016434893476686856335551:ℚ)/91109629336667060852050781250000000000000000000000000000),((25027537321606778239867043:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((906327293:ℚ)/1250000000),((7388021271:ℚ)/10000000000),((-1218888173:ℚ)/2550000000),((-676327293:ℚ)/1728125000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3043940857:ℚ)/10000000000),((8127786696687846483429699054721789587166633435469:ℚ)/37468953430652618408203125000000000000000000000000),((1544584326086313045496507:ℚ)/9241600000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((1462072141:ℚ)/2000000000),((7507484467:ℚ)/10000000000),((-53487360203:ℚ)/110600000000),((-1094072141:ℚ)/2812500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1384828361:ℚ)/5000000000),((98991394467368876751310448177037351227866295771353091:ℚ)/450540706515312194824218750000000000000000000000000000),((3903668790065457540697883:ℚ)/23658496000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((1485965329:ℚ)/2000000000),((3813461883:ℚ)/5000000000),((-27281156947:ℚ)/56250000000),((-85997333:ℚ)/220000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2120155407:ℚ)/10000000000),((65764758061425089050929308336789895049987302049417:ℚ)/299475000000000000000000000000000000000000000000000),((3802143356055049974095363:ℚ)/23658496000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((1887317149:ℚ)/2500000000),((2026116141:ℚ)/2500000000),((-14715045269:ℚ)/28600000000),((-1427317149:ℚ)/3812500000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1156081689:ℚ)/10000000000),((447773222081945880468259440651130270003045371617901451:ℚ)/1904900360107421875000000000000000000000000000000000000),((5780982948941306925483643:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((200670479:ℚ)/250000000),((8581705249:ℚ)/10000000000),((-63155347241:ℚ)/122000000000),((-154670479:ℚ)/405000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((985234549956693882770084586043476154389860604980317:ℚ)/4221080859375000000000000000000000000000000000000000),((158246521:ℚ)/1024000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((170081369:ℚ)/200000000),((10488528347:ℚ)/10000000000),((-80316755123:ℚ)/129600000000),((-133281369:ℚ)/400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4526953562195046946505900069888735738151463058811581:ℚ)/16200000000000000000000000000000000000000000000000000),((158246521:ℚ)/1024000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((10410917709:ℚ)/10000000000),((7148260257:ℚ)/5000000000),((-57294342313:ℚ)/80000000000),((-8570917709:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((629330605365141655103352354506334192577459186673132929183853:ℚ)/1904400000000000000000000000000000000000000000000000000000000),((158246521:ℚ)/1024000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source24 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source24 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC08
#check @N11Formalization.C450Source24GroupedC08.bound
#print axioms N11Formalization.C450Source24GroupedC08.valid0
#print axioms N11Formalization.C450Source24GroupedC08.valid1
#print axioms N11Formalization.C450Source24GroupedC08.valid2
#print axioms N11Formalization.C450Source24GroupedC08.valid3
#print axioms N11Formalization.C450Source24GroupedC08.valid4
#print axioms N11Formalization.C450Source24GroupedC08.valid5
#print axioms N11Formalization.C450Source24GroupedC08.valid6
#print axioms N11Formalization.C450Source24GroupedC08.valid7
#print axioms N11Formalization.C450Source24GroupedC08.valid8
#print axioms N11Formalization.C450Source24GroupedC08.valid9
#print axioms N11Formalization.C450Source24GroupedC08.valid10
#print axioms N11Formalization.C450Source24GroupedC08.valid11
#print axioms N11Formalization.C450Source24GroupedC08.valid12
#print axioms N11Formalization.C450Source24GroupedC08.valid13
#print axioms N11Formalization.C450Source24GroupedC08.bound
#print axioms N11Formalization.C450Source24GroupedC08.endpoint_checks
