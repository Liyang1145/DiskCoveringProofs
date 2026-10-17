import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((1172633117:ℚ)/2000000000),((6393676783:ℚ)/10000000000),((4726321429:ℚ)/7120000000),((20941030349:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6896493713:ℚ)/10000000000),((-127301057214004561443474264687361:ℚ)/5639752000000000000000000000000000),((-397317320538950969761807:ℚ)/1848320000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((633865241:ℚ)/1000000000),((828924279:ℚ)/1250000000),((7612517651:ℚ)/11060000000),((2706772837:ℚ)/3337500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((182630689:ℚ)/312500000),((-14097062901374259738909127284272875989553951346107037:ℚ)/528476178125000000000000000000000000000000000000000000),((-99226495985784880897703:ℚ)/462080000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((3288185349:ℚ)/5000000000),((84378093:ℚ)/125000000),((39370038839:ℚ)/56250000000),((39304897:ℚ)/49375000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((525023957:ℚ)/1000000000),((-73586235527528791546321933031069482472774637214863691:ℚ)/2574920654296875000000000000000000000000000000000000000),((-2479405105514988180944063:ℚ)/11552000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((418451519:ℚ)/625000000),((26832411:ℚ)/39062500),((384843593:ℚ)/550000000),((349488932:ℚ)/439453125),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((246464549:ℚ)/500000000),((-169126295554734231134039973552068597764654087381:ℚ)/5908203125000000000000000000000000000000000000000),((-38717194333940549080343:ℚ)/180500000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1362814893:ℚ)/2000000000),((436746483:ℚ)/625000000),((16270963823:ℚ)/23260000000),((1420239449:ℚ)/1787500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4587906173:ℚ)/10000000000),((-35231404672949417995621907139072905433706035868158089:ℚ)/1228935739843750000000000000000000000000000000000000000),((-396224078844719781560687:ℚ)/1848320000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((6932921349:ℚ)/10000000000),((704736581:ℚ)/1000000000),((82662134839:ℚ)/117250000000),((2290209743:ℚ)/2907500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((65954703:ℚ)/156250000),((-664327948572347949997279815080656239196317836318780791:ℚ)/22487467956542968750000000000000000000000000000000000000),((-9903153102361939846608063:ℚ)/46208000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1748085903:ℚ)/2500000000),((3553393567:ℚ)/5000000000),((20828944933:ℚ)/29550000000),((24605929:ℚ)/31250000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1006501163:ℚ)/2500000000),((-2757903751801381941426107084760041289210942990231113:ℚ)/93327307128906250000000000000000000000000000000000000),((-618760605661468721746167:ℚ)/2888000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((1410353023:ℚ)/2000000000),((3583103859:ℚ)/5000000000),((16793883253:ℚ)/23830000000),((11629311577:ℚ)/14775000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1910765821:ℚ)/5000000000),((-156249162411034823167236097991844649813987091645238019:ℚ)/5286060893359375000000000000000000000000000000000000000),((-395887639911900773944727:ℚ)/1848320000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((56889487:ℚ)/80000000),((361281379:ℚ)/500000000),((676984357:ℚ)/960800000),((1171844137:ℚ)/1489375000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((360608329:ℚ)/1000000000),((-640216465363726285387588244986601421834758905891:ℚ)/21654045012500000000000000000000000000000000000000),((-633229889466542417847:ℚ)/2957312000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((7170605911:ℚ)/10000000000),((3642523369:ℚ)/5000000000),((28425555007:ℚ)/40350000000),((11807570107:ℚ)/15012500000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3377555733:ℚ)/10000000000),((-28106346124983421200815927084999963744461668819172563:ℚ)/950444775390625000000000000000000000000000000000000000),((-9891247764870219896767623:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((3615012619:ℚ)/5000000000),((7344465207:ℚ)/10000000000),((42965138809:ℚ)/61000000000),((23793395621:ℚ)/30262500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1566541897:ℚ)/5000000000),((-42990713229902150466894117717961629960829728062474323:ℚ)/1453515625000000000000000000000000000000000000000000000),((-2472070805686267255563743:ℚ)/11552000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((58315551:ℚ)/80000000),((7463300143:ℚ)/10000000000),((692671061:ℚ)/991200000),((24149900429:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2868588979:ℚ)/10000000000),((-304249037249587909048522229938585295805868370323:ℚ)/10566749550000000000000000000000000000000000000000),((-632434663642401302743:ℚ)/2957312000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((3704139569:ℚ)/5000000000),((7582132511:ℚ)/10000000000),((43945535259:ℚ)/62900000000),((24506397533:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((70341259:ℚ)/312500000),((-2735373936512250875812401992125566872073384251019477:ℚ)/94931865310668945312500000000000000000000000000000000),((-2468971545409230698319543:ℚ)/11552000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((470444489:ℚ)/625000000),((3909894997:ℚ)/5000000000),((5574889379:ℚ)/8100000000),((12609684991:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1386067719:ℚ)/10000000000),((-23375776551856634238667952182749274428984881368279:ℚ)/854296875000000000000000000000000000000000000000000),((-38578128251673802353223:ℚ)/180500000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((3882384957:ℚ)/5000000000),((4860390181:ℚ)/5000000000),((45906234527:ℚ)/80000000000),((15461170543:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-158133013428155924469612385964545947733085176729182449:ℚ)/12500000000000000000000000000000000000000000000000000000),((-3419921:ℚ)/16000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((96657641:ℚ)/100000000),((13521942599:ℚ)/10000000000),((1127234051:ℚ)/2208000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-60335270187332447373717113711:ℚ)/18688512000000000000000000000000),((-3419921:ℚ)/16000000)⟩
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
end N11Formalization.C450Source12GroupedC28
#check @N11Formalization.C450Source12GroupedC28.bound
#print axioms N11Formalization.C450Source12GroupedC28.valid0
#print axioms N11Formalization.C450Source12GroupedC28.valid1
#print axioms N11Formalization.C450Source12GroupedC28.valid2
#print axioms N11Formalization.C450Source12GroupedC28.valid3
#print axioms N11Formalization.C450Source12GroupedC28.valid4
#print axioms N11Formalization.C450Source12GroupedC28.valid5
#print axioms N11Formalization.C450Source12GroupedC28.valid6
#print axioms N11Formalization.C450Source12GroupedC28.valid7
#print axioms N11Formalization.C450Source12GroupedC28.valid8
#print axioms N11Formalization.C450Source12GroupedC28.valid9
#print axioms N11Formalization.C450Source12GroupedC28.valid10
#print axioms N11Formalization.C450Source12GroupedC28.valid11
#print axioms N11Formalization.C450Source12GroupedC28.valid12
#print axioms N11Formalization.C450Source12GroupedC28.valid13
#print axioms N11Formalization.C450Source12GroupedC28.valid14
#print axioms N11Formalization.C450Source12GroupedC28.valid15
#print axioms N11Formalization.C450Source12GroupedC28.bound
#print axioms N11Formalization.C450Source12GroupedC28.endpoint_checks
