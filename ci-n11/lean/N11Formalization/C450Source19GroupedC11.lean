import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((12757519:ℚ)/20000000),((1668201141:ℚ)/2500000000),((-3644603423:ℚ)/12400000000),((-8149519:ℚ)/41200000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2873913477:ℚ)/5000000000),((3207830257230936481405508422820448518997903595561:ℚ)/40649444400000000000000000000000000000000000000000),((405047973106308638781:ℚ)/5914624000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((6617510731:ℚ)/10000000000),((345577269:ℚ)/500000000),((-764731807:ℚ)/2575000000),((-4313510731:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2570607319:ℚ)/5000000000),((122930155438396643077660456016644199172977396302880986639:ℚ)/1568415031200000000000000000000000000000000000000000000000),((92884851080831143245857781:ℚ)/1478656000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6856172269:ℚ)/10000000000),((1757720753:ℚ)/2500000000),((-3913162259:ℚ)/13350000000),((-4552172269:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((446120131:ℚ)/1000000000),((437570993196029984027973226156841264460808803567001816943:ℚ)/5715426488350000000000000000000000000000000000000000000000),((84469558889509829626191781:ℚ)/1478656000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((697547237:ℚ)/1000000000),((1418108827:ℚ)/2000000000),((-3166326481:ℚ)/10870000000),((-467147237:ℚ)/2193000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4082290241:ℚ)/10000000000),((452064701584687713487462553868727370242690413552578171:ℚ)/5970960668207812500000000000000000000000000000000000000),((802475159672875173227349:ℚ)/14786560000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7035115223:ℚ)/10000000000),((1787550077:ℚ)/2500000000),((-4002650231:ℚ)/13706250000),((-4731115223:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3879855439:ℚ)/10000000000),((175317758418487525181126418744885762471435206506313309077:ℚ)/2317896517256250000000000000000000000000000000000000000000),((78132880964068920352696109:ℚ)/1478656000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1773688361:ℚ)/2500000000),((7209851659:ℚ)/10000000000),((-16189554977:ℚ)/55300000000),((-52073407:ℚ)/242500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((45835899:ℚ)/125000000),((232778868109633319226188272611796365999141455068573:ℚ)/3080494195556640625000000000000000000000000000000000),((13160635708878633919781:ℚ)/256000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((447149197:ℚ)/625000000),((726949831:ℚ)/1000000000),((-1636849493:ℚ)/5577500000),((-303149197:ℚ)/1406250000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1720688489:ℚ)/5000000000),((34306639930944005566471251192258357143164776580405187:ℚ)/454410631209611892700195312500000000000000000000000000),((288657675809646417538789:ℚ)/5776000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7214016463:ℚ)/10000000000),((3664570191:ℚ)/5000000000),((-8273710573:ℚ)/28125000000),((-4910016463:ℚ)/22690000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((640144473:ℚ)/2000000000),((41304344028826551467296424286586060244560208288290967:ℚ)/547576458234375000000000000000000000000000000000000000),((198821265588269682016309:ℚ)/4096000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((7273641487:ℚ)/10000000000),((1847194497:ℚ)/2500000000),((-4181583491:ℚ)/14181250000),((-4969641487:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((735295969:ℚ)/2500000000),((12801739815737578603807941249298117507482046778340026266201:ℚ)/169856657484800000000000000000000000000000000000000000000000),((69650164113505375182604349:ℚ)/1478656000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3666631167:ℚ)/5000000000),((3754020123:ℚ)/5000000000),((-8542060369:ℚ)/28600000000),((-2514631167:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1328614041:ℚ)/5000000000),((9704763833209203184643536304348012888804255715524087193:ℚ)/127809316943750000000000000000000000000000000000000000000),((50642567509024590248160407:ℚ)/1108992000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((58222593:ℚ)/78125000),((1906821483:ℚ)/2500000000),((-4360464449:ℚ)/14537500000),((-13407531:ℚ)/61562500),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1973427053:ℚ)/10000000000),((32138611160352513231014594661880675743565562791239:ℚ)/423983039808273315429687500000000000000000000000000),((32087912300289897167:ℚ)/750000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((7571705967:ℚ)/10000000000),((7865730711:ℚ)/10000000000),((-18157192133:ℚ)/59100000000),((-5267705967:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((215789579:ℚ)/2500000000),((1374506128816574781090665522814425634354562057115013752393:ℚ)/17886102800000000000000000000000000000000000000000000000000),((176976356375472291780742007:ℚ)/4435968000000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((7810090487:ℚ)/10000000000),((8342453161:ℚ)/10000000000),((-19587359483:ℚ)/61000000000),((-5506090487:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2856281333098032320386460369350555398286004770931798783:ℚ)/36279705600000000000000000000000000000000000000000000000),((4015031:ℚ)/102400000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((2071675783:ℚ)/2500000000),((5123850069:ℚ)/5000000000),((-12651550207:ℚ)/32400000000),((-1495675783:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((7660854260738071796696204740528382832818352543918790727:ℚ)/86400000000000000000000000000000000000000000000000000000),((4015031:ℚ)/102400000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10191616003:ℚ)/10000000000),((14053849247:ℚ)/10000000000),((-36721547741:ℚ)/80000000000),((-7887616003:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((40784304426180165369772498028221146029833895881586411803:ℚ)/403671859200000000000000000000000000000000000000000000000),((4015031:ℚ)/102400000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC11
#check @N11Formalization.C450Source19GroupedC11.bound
#print axioms N11Formalization.C450Source19GroupedC11.valid0
#print axioms N11Formalization.C450Source19GroupedC11.valid1
#print axioms N11Formalization.C450Source19GroupedC11.valid2
#print axioms N11Formalization.C450Source19GroupedC11.valid3
#print axioms N11Formalization.C450Source19GroupedC11.valid4
#print axioms N11Formalization.C450Source19GroupedC11.valid5
#print axioms N11Formalization.C450Source19GroupedC11.valid6
#print axioms N11Formalization.C450Source19GroupedC11.valid7
#print axioms N11Formalization.C450Source19GroupedC11.valid8
#print axioms N11Formalization.C450Source19GroupedC11.valid9
#print axioms N11Formalization.C450Source19GroupedC11.valid10
#print axioms N11Formalization.C450Source19GroupedC11.valid11
#print axioms N11Formalization.C450Source19GroupedC11.valid12
#print axioms N11Formalization.C450Source19GroupedC11.valid13
#print axioms N11Formalization.C450Source19GroupedC11.valid14
#print axioms N11Formalization.C450Source19GroupedC11.bound
#print axioms N11Formalization.C450Source19GroupedC11.endpoint_checks
