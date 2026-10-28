import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((2707672791:ℚ)/5000000000),((5974513691:ℚ)/10000000000),((13973248761:ℚ)/17800000000),((48861595837:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7776768081:ℚ)/10000000000),((-1984341828535557561679355892831116703:ℚ)/8812112500000000000000000000000000000),((-1720867116726377325033259:ℚ)/5120000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((2945695309:ℚ)/5000000000),((24850533:ℚ)/40000000),((45014039017:ℚ)/55300000000),((202113731:ℚ)/213600000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3418958219:ℚ)/5000000000),((-66648374497656936974025453569144919893626478362613992921:ℚ)/264238089062500000000000000000000000000000000000000000000),((-29224069895745383279593:ℚ)/88719360000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((1532339779:ℚ)/2500000000),((253267091:ℚ)/400000000),((23280417127:ℚ)/28125000000),((2054469637:ℚ)/2212000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6325972637:ℚ)/10000000000),((-1023704048504351527032659620829573559577438562512641751:ℚ)/3862380981445312500000000000000000000000000000000000000),((-964178807720607574751699:ℚ)/2957312000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6248331463:ℚ)/10000000000),((6450711499:ℚ)/10000000000),((94668309019:ℚ)/114400000000),((5799442277:ℚ)/6250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((6056207563:ℚ)/10000000000),((-56296562836994118233522441949687304176888364543417697377:ℚ)/212669600000000000000000000000000000000000000000000000000),((-596372745900580399358584579:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1591824101:ℚ)/2500000000),((6569736403:ℚ)/10000000000),((24053713313:ℚ)/29075000000),((53028154821:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1155102339:ℚ)/2000000000),((-2538520537199919542394515397115759680944833364673360209:ℚ)/9601060467529296875000000000000000000000000000000000000),((-590117741481686257829257811:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((202695447:ℚ)/312500000),((6629245503:ℚ)/10000000000),((3055040811:ℚ)/3664062500),((53444718521:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2741090797:ℚ)/5000000000),((-742249522484607886812637290041848145315964251195769:ℚ)/2745052240788936614990234375000000000000000000000000),((-1760952703911729382724143633:ℚ)/5544960000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6545730721:ℚ)/10000000000),((167218811:ℚ)/250000000),((98534499373:ℚ)/118200000000),((1346531677:ℚ)/1465625000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1332530663:ℚ)/2500000000),((-19365568460476319015180971670196828105871902295274152309:ℚ)/71675371875000000000000000000000000000000000000000000000),((-364904200962873811375459:ℚ)/1155200000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6605205503:ℚ)/10000000000),((3374128633:ℚ)/5000000000),((99307671539:ℚ)/119150000000),((27138900431:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5174043391:ℚ)/10000000000),((-713562483872738520504745510487496516841437511981527733763:ℚ)/2643030446679687500000000000000000000000000000000000000000),((-145176299973480014743229931:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((666467869:ℚ)/1000000000),((212742501:ℚ)/312500000),((10008082297:ℚ)/12010000000),((1709197507:ℚ)/1861718750),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1002713031:ℚ)/2000000000),((-45639070148139961717955624555727503283504476086632641:ℚ)/169172226660156250000000000000000000000000000000000000),((-1692069338196854251949737:ℚ)/5415000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((84051879:ℚ)/125000000),((3433630393:ℚ)/5000000000),((420224809:ℚ)/504375000),((27555412751:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2424123939:ℚ)/5000000000),((-6005260900430776265572573995311721359384670369497:ℚ)/22276049423217773437500000000000000000000000000000),((-143602530514457826239844971:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((678362043:ℚ)/1000000000),((865844947:ℚ)/1250000000),((10162706559:ℚ)/12200000000),((6940914629:ℚ)/7565625000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((467757517:ℚ)/1000000000),((-764340899195715577848335088100291630190348717391817623:ℚ)/2837262500000000000000000000000000000000000000000000000),((-8925883775405365633155411:ℚ)/28880000000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1368617811:ℚ)/2000000000),((3522875721:ℚ)/5000000000),((6826677181:ℚ)/8260000000),((28180130047:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((4500934417:ℚ)/10000000000),((-57963246490577903952171023384346148049572601256649157:ℚ)/220140615625000000000000000000000000000000000000000000),((-423703040829711002763486817:ℚ)/1386240000000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1740505497:ℚ)/2500000000),((7164735981:ℚ)/10000000000),((25986571461:ℚ)/31450000000),((57193151867:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((515830467:ℚ)/1250000000),((-734496926066581767016080107147551002576715638091869:ℚ)/2792113685607910156250000000000000000000000000000000),((-1675806391064443414653544057:ℚ)/5544960000000000000000000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((7080949383:ℚ)/10000000000),((740268437:ℚ)/1000000000),((3907123777:ℚ)/4800000000),((5885879059:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((929300841:ℚ)/2500000000),((-4836205469928318209340661183274986657976014818627041:ℚ)/19200000000000000000000000000000000000000000000000000),((-5458833077562437344618051:ℚ)/18483200000000000000000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((1463757707:ℚ)/2000000000),((4177121009:ℚ)/5000000000),((21716850191:ℚ)/28960000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((1364404129:ℚ)/5000000000),((-468651983468886865986802566665153678102863557941070983:ℚ)/2371896400000000000000000000000000000000000000000000000),((-37069697:ℚ)/128000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((2067491703:ℚ)/2500000000),((9305503119:ℚ)/10000000000),((30237392139:ℚ)/40000000000),((72178521833:ℚ)/72400000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-5069321094014495621657879211148651441398615923170292307:ℚ)/25000000000000000000000000000000000000000000000000000000),((-37069697:ℚ)/128000000)⟩
theorem valid15 : Valid source23 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source23 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((2305230219:ℚ)/2500000000),((6554404543:ℚ)/5000000000),((11109330949:ℚ)/18400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-32029866231225293176080825722659991:ℚ)/389344000000000000000000000000000000),((-37069697:ℚ)/128000000)⟩
theorem valid16 : Valid source23 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source23 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source23 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC30
#check @N11Formalization.C450Source23GroupedC30.bound
#print axioms N11Formalization.C450Source23GroupedC30.valid0
#print axioms N11Formalization.C450Source23GroupedC30.valid1
#print axioms N11Formalization.C450Source23GroupedC30.valid2
#print axioms N11Formalization.C450Source23GroupedC30.valid3
#print axioms N11Formalization.C450Source23GroupedC30.valid4
#print axioms N11Formalization.C450Source23GroupedC30.valid5
#print axioms N11Formalization.C450Source23GroupedC30.valid6
#print axioms N11Formalization.C450Source23GroupedC30.valid7
#print axioms N11Formalization.C450Source23GroupedC30.valid8
#print axioms N11Formalization.C450Source23GroupedC30.valid9
#print axioms N11Formalization.C450Source23GroupedC30.valid10
#print axioms N11Formalization.C450Source23GroupedC30.valid11
#print axioms N11Formalization.C450Source23GroupedC30.valid12
#print axioms N11Formalization.C450Source23GroupedC30.valid13
#print axioms N11Formalization.C450Source23GroupedC30.valid14
#print axioms N11Formalization.C450Source23GroupedC30.valid15
#print axioms N11Formalization.C450Source23GroupedC30.valid16
#print axioms N11Formalization.C450Source23GroupedC30.bound
#print axioms N11Formalization.C450Source23GroupedC30.endpoint_checks
