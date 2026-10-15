import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((159100291:ℚ)/250000000),((1329599101:ℚ)/2000000000),((-7771193707:ℚ)/19840000000),((-373300873:ℚ)/1287500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((722927891:ℚ)/1250000000),((59785063695907721185008589662551015902824550216201939:ℚ)/1240522595214843750000000000000000000000000000000000000),((128049326030260390080153:ℚ)/1155200000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((206315717:ℚ)/312500000),((1721525513:ℚ)/2500000000),((-10130678591:ℚ)/25750000000),((-488947151:ℚ)/1668750000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2591145377:ℚ)/5000000000),((35876564997422728514779587006568823604697827793252367:ℚ)/747878566360473632812500000000000000000000000000000000),((196157653874334433414857:ℚ)/1805000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6840152023:ℚ)/10000000000),((1751284841:ℚ)/2500000000),((-10338993887:ℚ)/26700000000),((-16360456069:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2254904599:ℚ)/5000000000),((4178108708955904395243229036179035928100211818269477940139:ℚ)/89303538880468750000000000000000000000000000000000000000000),((196849867126740425647436577:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3479581059:ℚ)/5000000000),((7064654273:ℚ)/10000000000),((-41772579911:ℚ)/108700000000),((-8358743177:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4136016507:ℚ)/10000000000),((539128187344258741009170793867938172104908010476040145763:ℚ)/11662032555093383789062500000000000000000000000000000000000),((48710319131313849001718553:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((280746551:ℚ)/400000000),((712416677:ℚ)/1000000000),((-4218916739:ℚ)/10965000000),((-675839653:ℚ)/2212000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3936677877:ℚ)/10000000000),((107098437309792721467067808029678659699008007831609851:ℚ)/2317896517256250000000000000000000000000000000000000000),((310138841965747219798113:ℚ)/2957312000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7078163249:ℚ)/10000000000),((7183676917:ℚ)/10000000000),((-42605738419:ℚ)/110600000000),((-17074489747:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3727283329:ℚ)/10000000000),((1730899366235413331920878992415118346841772559190215169469:ℚ)/37480372877337646484375000000000000000000000000000000000000),((192832137988670142995843313:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7137660597:ℚ)/10000000000),((3621592387:ℚ)/5000000000),((-21511146709:ℚ)/55775000000),((-17252981791:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((701205457:ℚ)/2000000000),((1342401693779737022530680372077556440628848452943118926477:ℚ)/29082280397415161132812500000000000000000000000000000000000),((191827360862042735171851017:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((224911121:ℚ)/312500000),((7302690399:ℚ)/10000000000),((-4826536977:ℚ)/12500000000),((-544733363:ℚ)/1772656250),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((817624681:ℚ)/2500000000),((2007755535014992455779412943778234214667711373411:ℚ)/43517467040568590164184570312500000000000000000000),((186350042941563432663633:ℚ)/1805000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((3628324563:ℚ)/5000000000),((7362193847:ℚ)/10000000000),((-43855356929:ℚ)/113450000000),((-8804973689:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((24138819:ℚ)/80000000),((15298888517436858246367093921835521157859763055616037428179:ℚ)/331751284150000000000000000000000000000000000000000000000000),((47454346614686918516898297:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7316140411:ℚ)/10000000000),((1855423793:ℚ)/2500000000),((-11067966551:ℚ)/28600000000),((-17788421233:ℚ)/57675000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2741707241:ℚ)/10000000000),((926219912799611702601477111163987983531394392559492883:ℚ)/20093711097896575927734375000000000000000000000000000000),((188812187460914164825887273:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((295025191:ℚ)/400000000),((1870298607:ℚ)/2500000000),((-3724030083:ℚ)/9612500000),((-718675573:ℚ)/2326000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((487186327:ℚ)/2000000000),((2786779375449872092130952730276015403828976789912151563:ℚ)/60483301372150000000000000000000000000000000000000000000),((300490953895622525543553:ℚ)/2957312000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((1487023453:ℚ)/2000000000),((475011683:ℚ)/625000000),((-2845081781:ℚ)/7268750000),((-3629070359:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((521703939:ℚ)/2500000000),((5168284957957375247679270256454165274580570747576756409:ℚ)/111144609987500000000000000000000000000000000000000000000),((7472054474109619249299417:ℚ)/73932800000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((1510817361:ℚ)/2000000000),((7838149203:ℚ)/10000000000),((-15729014807:ℚ)/39400000000),((-3700452083:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((549877369:ℚ)/5000000000),((317295429984779408785537877270538725617751915440163487883:ℚ)/6707288550000000000000000000000000000000000000000000000000),((7391598440381610640327473:ℚ)/73932800000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((3896002659:ℚ)/5000000000),((2078498053:ℚ)/2500000000),((-12629486371:ℚ)/30500000000),((-9608007977:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((210752537339232493486691371943770342437841447888082466089:ℚ)/4322386800000000000000000000000000000000000000000000000000),((12743319:ℚ)/128000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((413388427:ℚ)/500000000),((10216561833:ℚ)/10000000000),((-21278644277:ℚ)/43200000000),((-1032165281:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((202317797087392770932857877891377391652075533245495951:ℚ)/3600000000000000000000000000000000000000000000000000000),((12743319:ℚ)/128000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((2542523773:ℚ)/2500000000),((3504893963:ℚ)/2500000000),((-22614257741:ℚ)/40000000000),((-6587571319:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6341950358939664558230403751439877512110027535585750923:ℚ)/98552700000000000000000000000000000000000000000000000000),((12743319:ℚ)/128000000)⟩
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
end N11Formalization.C450Source14GroupedC10
#check @N11Formalization.C450Source14GroupedC10.bound
#print axioms N11Formalization.C450Source14GroupedC10.valid0
#print axioms N11Formalization.C450Source14GroupedC10.valid1
#print axioms N11Formalization.C450Source14GroupedC10.valid2
#print axioms N11Formalization.C450Source14GroupedC10.valid3
#print axioms N11Formalization.C450Source14GroupedC10.valid4
#print axioms N11Formalization.C450Source14GroupedC10.valid5
#print axioms N11Formalization.C450Source14GroupedC10.valid6
#print axioms N11Formalization.C450Source14GroupedC10.valid7
#print axioms N11Formalization.C450Source14GroupedC10.valid8
#print axioms N11Formalization.C450Source14GroupedC10.valid9
#print axioms N11Formalization.C450Source14GroupedC10.valid10
#print axioms N11Formalization.C450Source14GroupedC10.valid11
#print axioms N11Formalization.C450Source14GroupedC10.valid12
#print axioms N11Formalization.C450Source14GroupedC10.valid13
#print axioms N11Formalization.C450Source14GroupedC10.valid14
#print axioms N11Formalization.C450Source14GroupedC10.valid15
#print axioms N11Formalization.C450Source14GroupedC10.bound
#print axioms N11Formalization.C450Source14GroupedC10.endpoint_checks
