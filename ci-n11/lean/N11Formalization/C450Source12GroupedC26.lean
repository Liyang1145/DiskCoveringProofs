import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((2957739287:ℚ)/5000000000),((1610450521:ℚ)/2500000000),((29819653583:ℚ)/53400000000),((1786450521:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((678759013:ℚ)/1000000000),((-2295044159074875366950081562083507:ℚ)/264363375000000000000000000000000000),((-3625668285890784312373209:ℚ)/18483200000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6391157061:ℚ)/10000000000),((3339792039:ℚ)/5000000000),((63920413549:ℚ)/110600000000),((3691792039:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2858875777:ℚ)/5000000000),((-6264939758529343182149210814307361540982993423392136163:ℚ)/528476178125000000000000000000000000000000000000000000000),((-43775281126231863975695843:ℚ)/221798400000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((662896127:ℚ)/1000000000),((3399233959:ℚ)/5000000000),((6606065143:ℚ)/11250000000),((3751233959:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1277623439:ℚ)/2500000000),((-273939450012306705611503455811938162346873059952523:ℚ)/20599365234375000000000000000000000000000000000000000),((-146365849060748969418569:ℚ)/739328000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6747855653:ℚ)/10000000000),((3458673653:ℚ)/5000000000),((67130700877:ℚ)/114400000000),((1270224551:ℚ)/1875000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4780890411:ℚ)/10000000000),((-711695652797685659940529827834676674142489752835744289:ℚ)/53167400000000000000000000000000000000000000000000000000),((-14659067571715080683575649:ℚ)/73932800000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((429171577:ℚ)/625000000),((7036222459:ℚ)/10000000000),((4262544193:ℚ)/7268750000),((7740222459:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4428848949:ℚ)/10000000000),((-504972169178401450675758076576066641197653204804519:ℚ)/37504142451286315917968750000000000000000000000000000),((-57349989171063758333369:ℚ)/288800000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((9:ℚ)/16),((5:ℚ)/8),((6985630243:ℚ)/10000000000),((443478657:ℚ)/625000000),((69270672187:ℚ)/117250000000),((487478657:ℚ)/726875000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2024245121:ℚ)/5000000000),((-317364017978380217615206345310182232598781644041403667:ℚ)/22487467956542968750000000000000000000000000000000000000),((-14704173913365131025028689:ℚ)/73932800000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1409014221:ℚ)/2000000000),((7155093583:ℚ)/10000000000),((13961127989:ℚ)/23640000000),((7859093583:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3845081481:ℚ)/10000000000),((-675614309074015226354629159351996945119023475860281:ℚ)/47783581250000000000000000000000000000000000000000000),((-1765857588445608604662803:ℚ)/8871936000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((3552255453:ℚ)/5000000000),((3607263847:ℚ)/5000000000),((35170299077:ℚ)/59575000000),((3959263847:ℚ)/5910000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1815446671:ℚ)/5000000000),((-1169816338515922981634603943020374999923207508048988051:ℚ)/82594701458740234375000000000000000000000000000000000000),((-11045098248618309675567347:ℚ)/55449600000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((895493709:ℚ)/1250000000),((1818490217:ℚ)/2500000000),((8859443381:ℚ)/15012500000),((1994490217:ℚ)/2978750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3403887333:ℚ)/10000000000),((-1171801385645836871887699259100957104532797802036467:ℚ)/82603626298904418945312500000000000000000000000000000),((-690849712547600147269523:ℚ)/3465600000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((1805846857:ℚ)/2500000000),((916674141:ℚ)/1250000000),((17852621713:ℚ)/30262500000),((1004674141:ℚ)/1501250000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3161298881:ℚ)/10000000000),((-5696402191590096221969105431165135429564242397184477:ℚ)/400968889617919921875000000000000000000000000000000000),((-921841782277121178952089:ℚ)/4620800000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((3641412099:ℚ)/5000000000),((1478564899:ℚ)/2000000000),((35972708891:ℚ)/61000000000),((1619364899:ℚ)/2421000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((362401779:ℚ)/1250000000),((-20677211367100459571817925239234121904432362435611377:ℚ)/1453515625000000000000000000000000000000000000000000000),((-11070616211292167334626483:ℚ)/55449600000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1835565001:ℚ)/2500000000),((938960579:ℚ)/1250000000),((18120085009:ℚ)/30975000000),((1026960579:ℚ)/1525000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2611765447:ℚ)/10000000000),((-4417053426148150745965346984293929863058441300982607:ℚ)/322471604919433593750000000000000000000000000000000000),((-923261656280965261598361:ℚ)/4620800000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3730564407:ℚ)/5000000000),((3815270719:ℚ)/5000000000),((36775079663:ℚ)/62900000000),((4167270719:ℚ)/6195000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1914598903:ℚ)/10000000000),((-1304128573923644522008091577020837461454259568309961:ℚ)/94931865310668945312500000000000000000000000000000000),((-11096213735061962038961867:ℚ)/55449600000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((757999403:ℚ)/1000000000),((7868245643:ℚ)/10000000000),((7461994627:ℚ)/12960000000),((8572245643:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((725743783:ℚ)/10000000000),((-4958672335844752690206634758387444379232933374207:ℚ)/388800000000000000000000000000000000000000000000000),((-148177639836890254275649:ℚ)/739328000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7817714313:ℚ)/10000000000),((2442382439:ℚ)/2500000000),((76759428817:ℚ)/160000000000),((2618382439:ℚ)/3240000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-4000480632773654796515483829209533:ℚ)/1600000000000000000000000000000000000),((-25660679:ℚ)/128000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((9719099507:ℚ)/10000000000),((13571036571:ℚ)/10000000000),((93871895563:ℚ)/220800000000),((14275036571:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2248412547039501088211539:ℚ)/406272000000000000000000000),((-25660679:ℚ)/128000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC26
#check @N11Formalization.C450Source12GroupedC26.bound
#print axioms N11Formalization.C450Source12GroupedC26.valid0
#print axioms N11Formalization.C450Source12GroupedC26.valid1
#print axioms N11Formalization.C450Source12GroupedC26.valid2
#print axioms N11Formalization.C450Source12GroupedC26.valid3
#print axioms N11Formalization.C450Source12GroupedC26.valid4
#print axioms N11Formalization.C450Source12GroupedC26.valid5
#print axioms N11Formalization.C450Source12GroupedC26.valid6
#print axioms N11Formalization.C450Source12GroupedC26.valid7
#print axioms N11Formalization.C450Source12GroupedC26.valid8
#print axioms N11Formalization.C450Source12GroupedC26.valid9
#print axioms N11Formalization.C450Source12GroupedC26.valid10
#print axioms N11Formalization.C450Source12GroupedC26.valid11
#print axioms N11Formalization.C450Source12GroupedC26.valid12
#print axioms N11Formalization.C450Source12GroupedC26.valid13
#print axioms N11Formalization.C450Source12GroupedC26.valid14
#print axioms N11Formalization.C450Source12GroupedC26.valid15
#print axioms N11Formalization.C450Source12GroupedC26.bound
#print axioms N11Formalization.C450Source12GroupedC26.endpoint_checks
