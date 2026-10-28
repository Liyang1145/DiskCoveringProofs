import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((150100291:ℚ)/250000000),((6524401477:ℚ)/10000000000),((185300291:ℚ)/534000000),((23413204431:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1649962079:ℚ)/2500000000),((84753802895251507311998356030455054523:ℚ)/4887058636800000000000000000000000000000),((-75990778855847354130249:ℚ)/462080000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6480152023:ℚ)/10000000000),((1690588089:ℚ)/2500000000),((7888152023:ℚ)/22120000000),((2010588089:ℚ)/4450000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5497568623:ℚ)/10000000000),((1487092499992607211337558612012004458674478308477899261357:ℚ)/101055874181718750000000000000000000000000000000000000000000),((-124871844327397540250453841:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((6718163249:ℚ)/10000000000),((3440658171:ℚ)/5000000000),((2708721083:ℚ)/7500000000),((12241974513:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4865123907:ℚ)/10000000000),((461277311871860016144558523825431779431201095638950049:ℚ)/33973468593750000000000000000000000000000000000000000000),((-126517205974961552794858529:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((213661121:ℚ)/312500000),((3500136601:ℚ)/5000000000),((257661121:ℚ)/715000000),((4140136601:ℚ)/9375000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((451884589:ℚ)/1000000000),((282355296062839897617607810543108093188668755614446296039:ℚ)/21061820983886718750000000000000000000000000000000000000000),((-124355873245424738617089:ℚ)/722000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((6956140411:ℚ)/10000000000),((705974907:ℚ)/1000000000),((8364140411:ℚ)/23070000000),((2501924721:ℚ)/5720000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4145897977:ℚ)/10000000000),((1338486675658116574807538549324943186263993442980947901237:ℚ)/103755718543620000000000000000000000000000000000000000000000),((-128163977902778278219573209:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((280625191:ℚ)/400000000),((3559611643:ℚ)/5000000000),((336945191:ℚ)/930400000),((4199611643:ℚ)/9612500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3947072411:ℚ)/10000000000),((770831647459613233883652881856420922043768399452472815277:ℚ)/60067352722511816406250000000000000000000000000000000000000),((-205721430240848571382449:ℚ)/1182924800000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/16),((3:ℚ)/8),((1415023453:ℚ)/2000000000),((717869589:ℚ)/1000000000),((242374779:ℚ)/670000000),((2537608767:ℚ)/5815000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3738273757:ℚ)/10000000000),((3522145113224976366849361499194179994507723547625912417:ℚ)/275834626807929687500000000000000000000000000000000000000),((-5159515990131603791783561:ℚ)/29573120000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7134602927:ℚ)/10000000000),((7238166921:ℚ)/10000000000),((2847534309:ℚ)/7880000000),((25554500763:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((109928823:ℚ)/312500000),((31055869997092025206314554585511480306493824894617337058613:ℚ)/2443605202991333007812500000000000000000000000000000000000000),((-129399995770051160458323041:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((1438817361:ℚ)/2000000000),((3648818209:ℚ)/5000000000),((1720417361:ℚ)/4766000000),((4288818209:ℚ)/9850000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((410380739:ℚ)/1250000000),((257495750058412294339494337917597071842430721831226526836637:ℚ)/20351107291873593750000000000000000000000000000000000000000000),((-5192487289850603145779809:ℚ)/29573120000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7253568943:ℚ)/10000000000),((229909513:ℚ)/312500000),((8661568943:ℚ)/24020000000),((809728539:ℚ)/1861718750),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((606192103:ℚ)/2000000000),((2345433597524810861766053899337480020003172743521569814471:ℚ)/186147937466856832504272460937500000000000000000000000000000),((-130224459477687868880090721:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((7313049381:ℚ)/10000000000),((7476036057:ℚ)/10000000000),((8721049381:ℚ)/24400000000),((26268108171:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1378344593:ℚ)/5000000000),((12973580862481027287971250028727454686942659606624585733349:ℚ)/1007183768643906250000000000000000000000000000000000000000000),((-130636827732645213435846169:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3716002659:ℚ)/5000000000),((3856941421:ℚ)/5000000000),((4420002659:ℚ)/12580000000),((13490824263:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((263311141:ℚ)/1250000000),((47059990701667466158363916938628818657547308456958200615193:ℚ)/3507929289882812500000000000000000000000000000000000000000000),((-32865459598696854956112649:ℚ)/184832000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((1917474621:ℚ)/2500000000),((31806837:ℚ)/40000000),((2269474621:ℚ)/6480000000),((110780511:ℚ)/251600000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1729639943046353190790904834215349958233881107795521:ℚ)/130620686242320000000000000000000000000000000000000000),((-45923703:ℚ)/256000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((395388427:ℚ)/500000000),((9853761497:ℚ)/10000000000),((465788427:ℚ)/1600000000),((11133761497:ℚ)/21600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((186146840310054617788617720261047:ℚ)/9600000000000000000000000000000000),((-45923703:ℚ)/256000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((2452523773:ℚ)/2500000000),((13656169067:ℚ)/10000000000),((2804523773:ℚ)/11040000000),((44808507201:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1653167706974741191325519:ℚ)/60940800000000000000000000),((-45923703:ℚ)/256000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC22
#check @N11Formalization.C450Source13GroupedC22.bound
#print axioms N11Formalization.C450Source13GroupedC22.valid0
#print axioms N11Formalization.C450Source13GroupedC22.valid1
#print axioms N11Formalization.C450Source13GroupedC22.valid2
#print axioms N11Formalization.C450Source13GroupedC22.valid3
#print axioms N11Formalization.C450Source13GroupedC22.valid4
#print axioms N11Formalization.C450Source13GroupedC22.valid5
#print axioms N11Formalization.C450Source13GroupedC22.valid6
#print axioms N11Formalization.C450Source13GroupedC22.valid7
#print axioms N11Formalization.C450Source13GroupedC22.valid8
#print axioms N11Formalization.C450Source13GroupedC22.valid9
#print axioms N11Formalization.C450Source13GroupedC22.valid10
#print axioms N11Formalization.C450Source13GroupedC22.valid11
#print axioms N11Formalization.C450Source13GroupedC22.valid12
#print axioms N11Formalization.C450Source13GroupedC22.valid13
#print axioms N11Formalization.C450Source13GroupedC22.valid14
#print axioms N11Formalization.C450Source13GroupedC22.bound
#print axioms N11Formalization.C450Source13GroupedC22.endpoint_checks
