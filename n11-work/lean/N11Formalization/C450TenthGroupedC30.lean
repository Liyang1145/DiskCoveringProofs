import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((5882549917:ℚ)/10000000000),((400774547:ℚ)/625000000),((27197716307:ℚ)/35600000000),((2985421829:ℚ)/3100000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3428154609:ℚ)/5000000000),((-7420896795252134356867206498496930989:ℚ)/281987600000000000000000000000000000000),((-1393913826190481539639661:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6357724329:ℚ)/10000000000),((1329996473:ℚ)/2000000000),((87770416277:ℚ)/110600000000),((9885975311:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2899269797:ℚ)/5000000000),((-108336152695334018526277378675196474945557434441853080443:ℚ)/3623836650000000000000000000000000000000000000000000000000),((-14209773275739189797998741:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((3297651271:ℚ)/5000000000),((67687749:ℚ)/100000000),((45429466523:ℚ)/56250000000),((502614243:ℚ)/553000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2600163151:ℚ)/5000000000),((-11713871762474282950558516483019520976574245440859148659:ℚ)/370788574218750000000000000000000000000000000000000000000),((-35444534984618251718429:ℚ)/184832000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((3357044833:ℚ)/5000000000),((3443783011:ℚ)/5000000000),((46201582829:ℚ)/57200000000),((25546481077:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2438287791:ℚ)/5000000000),((-3360078841229941901115681018510604975585244575528947549:ℚ)/106334800000000000000000000000000000000000000000000000000),((-88411562073993578674400909:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1708218889:ℚ)/2500000000),((7006355799:ℚ)/10000000000),((23486845557:ℚ)/29075000000),((51924490593:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2265863323:ℚ)/5000000000),((-1213807189699335241702090649692991710625690520143144687:ℚ)/38404241870117187500000000000000000000000000000000000000),((-352847026789915494576279029:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((6951660273:ℚ)/10000000000),((1766437551:ℚ)/2500000000),((95491583549:ℚ)/117250000000),((13085062857:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((4160508057:ℚ)/10000000000),((-34970859107385129290042199188588524981130433448756544291:ℚ)/1079398461914062500000000000000000000000000000000000000000),((-22027960682146318766485829:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((701105221:ℚ)/1000000000),((7125144297:ℚ)/10000000000),((3208789291:ℚ)/3940000000),((52756010079:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((990676581:ℚ)/2500000000),((-3095768750377384661369407824928980176935913372669641:ℚ)/95567162500000000000000000000000000000000000000000000),((-352047684888230300405740661:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3535221937:ℚ)/5000000000),((1436907617:ℚ)/2000000000),((48517885181:ℚ)/59575000000),((10634353319:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3755076541:ℚ)/10000000000),((-128407592496865315264344028591835588062834114757520801437:ℚ)/3964545670019531250000000000000000000000000000000000000000),((-14065918746599195699972581:ℚ)/73932800000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((891229409:ℚ)/1250000000),((905491447:ℚ)/1250000000),((12225982317:ℚ)/15012500000),((6698440129:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3535883801:ℚ)/10000000000),((-42801199611310987821762303265085946410321077069636287:ℚ)/1321658020782470703125000000000000000000000000000000000),((-5488253471738136256939061:ℚ)/28880000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7189226411:ℚ)/10000000000),((7303324777:ℚ)/10000000000),((98579943343:ℚ)/121050000000),((54003273439:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1651411269:ℚ)/5000000000),((-39885071647060663257953421515902685988970529174522829797:ℚ)/1231776428906250000000000000000000000000000000000000000000),((-350848445420377541062138741:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((453038581:ℚ)/625000000),((3681358847:ℚ)/5000000000),((6209501553:ℚ)/7625000000),((27209511929:ℚ)/30262500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((763178369:ℚ)/2500000000),((-89706049329855754728336106104417836658015300744273603:ℚ)/2770764160156250000000000000000000000000000000000000000),((-87612159578117934790631461:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3654003967:ℚ)/5000000000),((3711055167:ℚ)/5000000000),((50062051571:ℚ)/61475000000),((27417386169:ℚ)/30500000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((2780955843:ℚ)/10000000000),((-11751234578144013285004747308229896688652743335403264809:ℚ)/363007533666992187500000000000000000000000000000000000000),((-242416067050456571673821:ℚ)/1280000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((736739833:ℚ)/1000000000),((7481502703:ℚ)/10000000000),((3363205943:ℚ)/4130000000),((55250518921:ℚ)/61475000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((24804389:ℚ)/100000000),((-2035858784037214480285564186849890623093041324185099:ℚ)/62897318750000000000000000000000000000000000000000000),((-349648932905593881084318661:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((742678849:ℚ)/1000000000),((3800143327:ℚ)/5000000000),((10166825037:ℚ)/12580000000),((28041003289:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2139069413:ℚ)/10000000000),((-384450591331495221509783563537753745039967275050503:ℚ)/12151278759765625000000000000000000000000000000000000),((-24158659:ℚ)/128000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((7545568123:ℚ)/10000000000),((7837851569:ℚ)/10000000000),((34404128533:ℚ)/43200000000),((57744960983:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((18711751:ℚ)/156250000),((-62772993841872656082081694104199255220795843073237389:ℚ)/2073600000000000000000000000000000000000000000000000000),((-24158659:ℚ)/128000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((389156239:ℚ)/500000000),((9738259851:ℚ)/10000000000),((5315031107:ℚ)/8000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-10010144990386560597277017580882897301084546397106499:ℚ)/600000000000000000000000000000000000000000000000000000),((-24158659:ℚ)/128000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((2420870283:ℚ)/2500000000),((541549563:ℚ)/400000000),((32751313679:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-383264001509031158091302115693712447:ℚ)/42049152000000000000000000000000000000),((-24158659:ℚ)/128000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound tenth nn0 nn1 Qcell ((2459:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC30
#check @N11Formalization.C450TenthGroupedC30.bound
#print axioms N11Formalization.C450TenthGroupedC30.valid0
#print axioms N11Formalization.C450TenthGroupedC30.valid1
#print axioms N11Formalization.C450TenthGroupedC30.valid2
#print axioms N11Formalization.C450TenthGroupedC30.valid3
#print axioms N11Formalization.C450TenthGroupedC30.valid4
#print axioms N11Formalization.C450TenthGroupedC30.valid5
#print axioms N11Formalization.C450TenthGroupedC30.valid6
#print axioms N11Formalization.C450TenthGroupedC30.valid7
#print axioms N11Formalization.C450TenthGroupedC30.valid8
#print axioms N11Formalization.C450TenthGroupedC30.valid9
#print axioms N11Formalization.C450TenthGroupedC30.valid10
#print axioms N11Formalization.C450TenthGroupedC30.valid11
#print axioms N11Formalization.C450TenthGroupedC30.valid12
#print axioms N11Formalization.C450TenthGroupedC30.valid13
#print axioms N11Formalization.C450TenthGroupedC30.valid14
#print axioms N11Formalization.C450TenthGroupedC30.valid15
#print axioms N11Formalization.C450TenthGroupedC30.valid16
#print axioms N11Formalization.C450TenthGroupedC30.bound
#print axioms N11Formalization.C450TenthGroupedC30.endpoint_checks
