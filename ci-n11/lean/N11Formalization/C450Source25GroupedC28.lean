import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((680924769:ℚ)/1250000000),((6008981859:ℚ)/10000000000),((9330172459:ℚ)/13350000000),((21866945577:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((964559193:ℚ)/1250000000),((-4529094839988854783573346681481761:ℚ)/22030281250000000000000000000000000),((-3299548551683051626032587009:ℚ)/8871936000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((740591139:ℚ)/1250000000),((6247638991:ℚ)/10000000000),((9986502529:ℚ)/13825000000),((7527638991:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((846022457:ℚ)/1250000000),((-3817307160882056095454716459460054506785189095707933651:ℚ)/16514880566406250000000000000000000000000000000000000000),((-1086047543666178603397567603:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((1232654731:ℚ)/2000000000),((3183469019:ℚ)/5000000000),((5501067347:ℚ)/7500000000),((11470407057:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((390631473:ℚ)/625000000),((-71209339282932426853832794186277919759964800046873937:ℚ)/292968750000000000000000000000000000000000000000000000),((-747239197297263944934563:ℚ)/2048000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6282519299:ℚ)/10000000000),((259448749:ℚ)/400000000),((83827712289:ℚ)/114400000000),((103549583:ℚ)/125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1195346093:ℚ)/2000000000),((-206450370382501495560129987930678924050247070882037021489:ℚ)/850678400000000000000000000000000000000000000000000000000),((-1715024748007885020103563:ℚ)/4731699200000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3200874189:ℚ)/5000000000),((654585247:ℚ)/1000000000),((42569616079:ℚ)/57675000000),((2347755741:ℚ)/2860000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2845973083:ℚ)/5000000000),((-74440474733539994410977148693679643894521803232618228941:ℚ)/299766319409179687500000000000000000000000000000000000000),((-10682956999687752862290067:ℚ)/29573120000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1292271393:ℚ)/2000000000),((165137049:ℚ)/250000000),((17158985323:ℚ)/23260000000),((197137049:ℚ)/240312500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((5544719999:ℚ)/10000000000),((-780463097807378108749973218954856247501137955510473513:ℚ)/3146075494000000000000000000000000000000000000000000000),((-1996272618259986019693289:ℚ)/5544960000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((6520961713:ℚ)/10000000000),((66651073:ℚ)/100000000),((86450578843:ℚ)/117250000000),((238353219:ℚ)/290750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5393916877:ℚ)/10000000000),((-89166803975952758080652522934608230598125762936760309311:ℚ)/359799487304687500000000000000000000000000000000000000000),((-106103955519394572630227:ℚ)/295731200000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6580562717:ℚ)/10000000000),((6724728591:ℚ)/10000000000),((29035396629:ℚ)/39400000000),((24014185773:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5239224619:ℚ)/10000000000),((-23659911335508023458536531530021806546763659607933138479:ℚ)/95567162500000000000000000000000000000000000000000000000),((-3172134524405669537772923609:ℚ)/8871936000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6640160067:ℚ)/10000000000),((678434593:ℚ)/1000000000),((87761760737:ℚ)/119150000000),((806434593:ℚ)/985000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5080284599:ℚ)/10000000000),((-2614752117762912836189733606535715848395276255781260689387:ℚ)/10572121786718750000000000000000000000000000000000000000000),((-10536945871251940632282387:ℚ)/29573120000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1674938463:ℚ)/2500000000),((6843959413:ℚ)/10000000000),((22104323093:ℚ)/30025000000),((24371878239:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((983336289:ℚ)/2000000000),((-2612422609047145410373980525358243213586735662721997663:ℚ)/10573264166259765625000000000000000000000000000000000000),((-1049988790642508496832524347:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((6759344157:ℚ)/10000000000),((696317517:ℚ)/1000000000),((89072785727:ℚ)/122000000000),((2472952551:ℚ)/3002500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4747929621:ℚ)/10000000000),((-2737397560639854898035560417011564363000316734648989882117:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-31275316980811323998929121:ℚ)/88719360000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1375702931:ℚ)/2000000000),((7082376561:ℚ)/10000000000),((18076732241:ℚ)/24780000000),((25087129683:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((439257397:ℚ)/1000000000),((-1908569809534279070411032392892143009517759800067339553:ℚ)/7925062162500000000000000000000000000000000000000000000),((-3104830471050847854285175769:ℚ)/8871936000000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6997672189:ℚ)/10000000000),((7201564241:ℚ)/10000000000),((145778051:ℚ)/200000000),((8481564241:ℚ)/10325000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2004036191:ℚ)/5000000000),((-11740851393391997616941285898868008504637613841:ℚ)/48828125000000000000000000000000000000000000000),((-1027287553740729765209271603:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((889602169:ℚ)/1250000000),((74399009:ℚ)/100000000),((3875207953:ℚ)/5400000000),((261597027:ℚ)/314500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1792512059:ℚ)/5000000000),((-8377651241419748627021714494208763143604199912478561:ℚ)/36450000000000000000000000000000000000000000000000000),((-101170906078739487459603:ℚ)/295731200000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7355072753:ℚ)/10000000000),((292036183:ℚ)/312500000),((95625800283:ℚ)/160000000000),((332036183:ℚ)/337500000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1272828977:ℚ)/5000000000),((-202051418799192734373131899834319600801894436815031092577:ℚ)/1600000000000000000000000000000000000000000000000000000000),((-346621533:ℚ)/1024000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((1851963927:ℚ)/2000000000),((13151318641:ℚ)/10000000000),((23315603197:ℚ)/44160000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-431685799551977884092383372578268863:ℚ)/7176388608000000000000000000000000000),((-346621533:ℚ)/1024000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC28
#check @N11Formalization.C450Source25GroupedC28.bound
#print axioms N11Formalization.C450Source25GroupedC28.valid0
#print axioms N11Formalization.C450Source25GroupedC28.valid1
#print axioms N11Formalization.C450Source25GroupedC28.valid2
#print axioms N11Formalization.C450Source25GroupedC28.valid3
#print axioms N11Formalization.C450Source25GroupedC28.valid4
#print axioms N11Formalization.C450Source25GroupedC28.valid5
#print axioms N11Formalization.C450Source25GroupedC28.valid6
#print axioms N11Formalization.C450Source25GroupedC28.valid7
#print axioms N11Formalization.C450Source25GroupedC28.valid8
#print axioms N11Formalization.C450Source25GroupedC28.valid9
#print axioms N11Formalization.C450Source25GroupedC28.valid10
#print axioms N11Formalization.C450Source25GroupedC28.valid11
#print axioms N11Formalization.C450Source25GroupedC28.valid12
#print axioms N11Formalization.C450Source25GroupedC28.valid13
#print axioms N11Formalization.C450Source25GroupedC28.valid14
#print axioms N11Formalization.C450Source25GroupedC28.valid15
#print axioms N11Formalization.C450Source25GroupedC28.bound
#print axioms N11Formalization.C450Source25GroupedC28.endpoint_checks
