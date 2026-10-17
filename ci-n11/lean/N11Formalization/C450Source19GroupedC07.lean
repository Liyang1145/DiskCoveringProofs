import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((1311391189:ℚ)/2000000000),((6862917143:ℚ)/10000000000),((-5774917143:ℚ)/9920000000),((-9498520701:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((212039329:ℚ)/400000000),((4868984839388257963432375324664907139317992896046842188789:ℚ)/64727596851200000000000000000000000000000000000000000000000),((2177741122211319600593029:ℚ)/7393280000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((424712627:ℚ)/625000000),((349105703:ℚ)/500000000),((-294705703:ℚ)/515000000),((-3102413643:ℚ)/6556250000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((928615169:ℚ)/2000000000),((16974739613047044322634233858908497829132120565957649309:ℚ)/234851149126367187500000000000000000000000000000000000000),((210972816112593432069621:ℚ)/722000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((276583969:ℚ)/400000000),((7041706469:ℚ)/10000000000),((-5953706469:ℚ)/10490000000),((-69946749:ℚ)/146000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4279565947:ℚ)/10000000000),((37336664057276711990452375003638348784751539350355407471:ℚ)/526658796106250000000000000000000000000000000000000000000),((238403175488029650149:ℚ)/819200000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((6974191767:ℚ)/10000000000),((7101294989:ℚ)/10000000000),((-6013294989:ℚ)/10585000000),((-17082575301:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4086532669:ℚ)/10000000000),((14267634743896260806267646050903153150355215372179869159:ℚ)/201071152050976562500000000000000000000000000000000000000),((161038600597992388310475383:ℚ)/554496000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((7033780419:ℚ)/10000000000),((1790219931:ℚ)/2500000000),((-1518219931:ℚ)/2670000000),((-51784023771:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3884495173:ℚ)/10000000000),((18391969988569797847090042126301776788482343638297646379:ℚ)/258970103982641601562500000000000000000000000000000000000),((160707009841787360256293567:ℚ)/554496000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((1773341321:ℚ)/2500000000),((449416919:ℚ)/625000000),((-381416919:ℚ)/673437500),((-1453341321:ℚ)/3006250000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1835981553:ℚ)/5000000000),((1942065773555010209317703142928515053359555413836110863:ℚ)/27602096886561810970306396484375000000000000000000000000),((3341132849420912304011709:ℚ)/11552000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7123156327:ℚ)/10000000000),((3610230387:ℚ)/5000000000),((-3066230387:ℚ)/5411250000),((-52588406943:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((890294179:ℚ)/2500000000),((742048617135726071355857538576982670661752591494838846191:ℚ)/10541658018884655761718750000000000000000000000000000000000),((53402556420581215944329821:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7152946461:ℚ)/10000000000),((1812562487:ℚ)/2500000000),((-1540562487:ℚ)/2717500000),((-52856518149:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3446991223:ℚ)/10000000000),((10528225818165074274538795172272030982395226815182292881741:ℚ)/149497894714609173583984375000000000000000000000000000000000),((160040701036671909070706687:ℚ)/554496000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7182735697:ℚ)/10000000000),((1820009559:ℚ)/2500000000),((-1548009559:ℚ)/2729375000),((-17708207091:ℚ)/36550000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((33290563:ℚ)/100000000),((299017354698241669621400622982625952437142195410088749013:ℚ)/4244088352788118648529052734375000000000000000000000000000),((53291157353173186051124941:ℚ)/184832000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7212524047:ℚ)/10000000000),((7339612201:ℚ)/10000000000),((-6251612201:ℚ)/10965000000),((-53392716423:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((641391543:ℚ)/2000000000),((8408031752205917656610633382197295744075842653941788976659:ℚ)/118112936974296130371093750000000000000000000000000000000000),((53235327428932385601142541:ℚ)/184832000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1454419627:ℚ)/2000000000),((7399182761:ℚ)/10000000000),((-6311182761:ℚ)/11060000000),((-10785776643:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2948180807:ℚ)/10000000000),((26768741764867157467309449331931879552958162554242992494181:ℚ)/375773816918346875000000000000000000000000000000000000000000),((2124936269197728280991621:ℚ)/7393280000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((458229301:ℚ)/625000000),((7458750003:ℚ)/10000000000),((-6370750003:ℚ)/11155000000),((-378229301:ℚ)/781250000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2665200717:ℚ)/10000000000),((7247022359796677138976548723293909741356924401425123:ℚ)/101664664224243164062500000000000000000000000000000000),((207074758356375375718149:ℚ)/722000000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((295649447:ℚ)/400000000),((7577874861:ℚ)/10000000000),((-6489874861:ℚ)/11250000000),((-200004093:ℚ)/416000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2349281199:ℚ)/10000000000),((109292504811642248881234297837724827518965633409881021527:ℚ)/1503918457031250000000000000000000000000000000000000000000),((84637634490614933694941:ℚ)/295731200000000000000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((1502072253:ℚ)/2000000000),((3908044131:ℚ)/5000000000),((-3364044131:ℚ)/5720000000),((-3738216759:ℚ)/7880000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1537389277:ℚ)/10000000000),((854752109031500775944385773199565905252134533178304873777:ℚ)/11348554946300000000000000000000000000000000000000000000000),((6320669281056545849164223:ℚ)/22179840000000000000000000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((3874287553:ℚ)/5000000000),((4027128517:ℚ)/5000000000),((-1161042839:ℚ)/1970000000),((-29108587977:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((40156262581221925146574949341289434887319396027348416911:ℚ)/533408117493750000000000000000000000000000000000000000000),((18179031:ℚ)/64000000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7986744289:ℚ)/10000000000),((4265238237:ℚ)/5000000000),((-3721238237:ℚ)/6100000000),((-6706744289:ℚ)/14400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3060367300806085128226450420541324634051360072920918173:ℚ)/38303043750000000000000000000000000000000000000000000000),((18179031:ℚ)/64000000)⟩
theorem valid15 : Valid source19 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((6611691:ℚ)/7812500),((10434192509:ℚ)/10000000000),((-3115397503:ℚ)/4320000000),((-50505219:ℚ)/125000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((158229156628558188648564381549152128619768047621070263:ℚ)/1511654400000000000000000000000000000000000000000000000),((18179031:ℚ)/64000000)⟩
theorem valid16 : Valid source19 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10366682801:ℚ)/10000000000),((17798187:ℚ)/12500000),((-16438187:ℚ)/20000000),((-27260048403:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2609864298953953524096022163157147457456244075843:ℚ)/19837500000000000000000000000000000000000000000000),((18179031:ℚ)/64000000)⟩
theorem valid17 : Valid source19 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((4329:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source19 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC07
#check @N11Formalization.C450Source19GroupedC07.bound
#print axioms N11Formalization.C450Source19GroupedC07.valid0
#print axioms N11Formalization.C450Source19GroupedC07.valid1
#print axioms N11Formalization.C450Source19GroupedC07.valid2
#print axioms N11Formalization.C450Source19GroupedC07.valid3
#print axioms N11Formalization.C450Source19GroupedC07.valid4
#print axioms N11Formalization.C450Source19GroupedC07.valid5
#print axioms N11Formalization.C450Source19GroupedC07.valid6
#print axioms N11Formalization.C450Source19GroupedC07.valid7
#print axioms N11Formalization.C450Source19GroupedC07.valid8
#print axioms N11Formalization.C450Source19GroupedC07.valid9
#print axioms N11Formalization.C450Source19GroupedC07.valid10
#print axioms N11Formalization.C450Source19GroupedC07.valid11
#print axioms N11Formalization.C450Source19GroupedC07.valid12
#print axioms N11Formalization.C450Source19GroupedC07.valid13
#print axioms N11Formalization.C450Source19GroupedC07.valid14
#print axioms N11Formalization.C450Source19GroupedC07.valid15
#print axioms N11Formalization.C450Source19GroupedC07.valid16
#print axioms N11Formalization.C450Source19GroupedC07.valid17
#print axioms N11Formalization.C450Source19GroupedC07.bound
#print axioms N11Formalization.C450Source19GroupedC07.endpoint_checks
