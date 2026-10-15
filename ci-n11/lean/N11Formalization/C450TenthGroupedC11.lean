import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6292543901:ℚ)/10000000000),((6563843697:ℚ)/10000000000),((-17131531091:ℚ)/49600000000),((-5140543901:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5953249771:ℚ)/10000000000),((125590801667603596809560379208582605794262775871285867603:ℚ)/5081180550000000000000000000000000000000000000000000000000),((129927060642137212611235409:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((3265159647:ℚ)/5000000000),((3400826043:ℚ)/5000000000),((-8922478129:ℚ)/25750000000),((-896386549:ℚ)/3560000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((214795847:ℚ)/400000000),((178485741666881025930039973362555764758053034311819297:ℚ)/7261180700000000000000000000000000000000000000000000000),((32006486065385481038701449:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6768075057:ℚ)/10000000000),((346027409:ℚ)/500000000),((-10225643:ℚ)/30000000),((-5616075057:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4722738437:ℚ)/10000000000),((4632002830106998298329179201286955240377248719916965729:ℚ)/192654825450000000000000000000000000000000000000000000000),((315017048327596782921681:ℚ)/4620800000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6886946223:ℚ)/10000000000),((1744998581:ℚ)/2500000000),((-4594995743:ℚ)/13587500000),((-1911648741:ℚ)/7310000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((545801701:ℚ)/1250000000),((15784393461767595800325163054834336585175443220594778337:ℚ)/663440074245312500000000000000000000000000000000000000000),((7812382837959194203073961:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((1736595057:ℚ)/2500000000),((1407887849:ℚ)/2000000000),((-3711663547:ℚ)/10965000000),((-206942151:ℚ)/790000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4177664919:ℚ)/10000000000),((2510262735970968083970557391443057439812984989182517:ℚ)/105589309277343750000000000000000000000000000000000000),((4981035907817779849443201:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7005813219:ℚ)/10000000000),((1774720743:ℚ)/2500000000),((-4684162229:ℚ)/13825000000),((-5853813219:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3980527847:ℚ)/10000000000),((8140848508494855410594292690905478211217677780216892599:ℚ)/342677694878515625000000000000000000000000000000000000000),((7753388611721418074015649:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((353262261:ℚ)/500000000),((7158325537:ℚ)/10000000000),((-18914976611:ℚ)/55775000000),((-98554087:ℚ)/375000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((754736823:ℚ)/2000000000),((204566446220638411365549771987965296432303516396649:ℚ)/8616971969604492187500000000000000000000000000000000),((123583085469706753917729969:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((3562338129:ℚ)/5000000000),((898505799:ℚ)/1250000000),((-2375517397:ℚ)/7031250000),((-2986338129:ℚ)/11297500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3555435939:ℚ)/10000000000),((1916142382606369667127484135566314099897322611679597619:ℚ)/81109098948339843750000000000000000000000000000000000000),((1923121710633508508964801:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7154391423:ℚ)/10000000000),((902220871:ℚ)/1250000000),((-2386662613:ℚ)/7060937500),((-6002391423:ℚ)/22690000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3441360321:ℚ)/10000000000),((19480159622204072318805123751119581818991795479455077707:ℚ)/824832671587046875000000000000000000000000000000000000000),((5317025948746556323881:ℚ)/80000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((1436821271:ℚ)/2000000000),((1811871817:ℚ)/2500000000),((-4795615451:ℚ)/14181250000),((-1206421271:ℚ)/4557000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((332353307:ℚ)/1000000000),((1508793978992797976011943622497407044291717644654280341:ℚ)/63904626992981250000000000000000000000000000000000000000),((7663092645394764159641089:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((7213821059:ℚ)/10000000000),((3638603647:ℚ)/5000000000),((-310832611:ℚ)/918750000),((-6061821059:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((640307887:ℚ)/2000000000),((37105516945856833577819454088308838162764019670380744309:ℚ)/1572053683200000000000000000000000000000000000000000000000),((30593633463338024988228209:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7243535537:ℚ)/10000000000),((7336646543:ℚ)/10000000000),((-19449939629:ℚ)/57200000000),((-6091535537:ℚ)/23070000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3074882993:ℚ)/10000000000),((2769999309563740707169423689613759806527995299554813:ℚ)/116908864569580078125000000000000000000000000000000000),((122172971766980304318714449:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((456435239:ℚ)/625000000),((369804237:ℚ)/500000000),((-981412711:ℚ)/2883750000),((-384435239:ℚ)/1453750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((87657207:ℚ)/312500000),((1048980047798855420007292877690482495098378357562884607:ℚ)/44299292997180175781250000000000000000000000000000000000),((304260068984202224863769:ℚ)/4620800000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((184059781:ℚ)/250000000),((3757479041:ℚ)/5000000000),((-9992437123:ℚ)/29075000000),((-155259781:ℚ)/591000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2507133507:ℚ)/10000000000),((331399466604120064655443942086267043003550402088399:ℚ)/13893076248437500000000000000000000000000000000000000),((30325902658207686521908081:ℚ)/462080000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((7481243541:ℚ)/10000000000),((7752693223:ℚ)/10000000000),((-20698079669:ℚ)/59100000000),((-6329243541:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1770125129:ℚ)/10000000000),((1297662981284347582236268891926857859661951752307847121601:ℚ)/53658308400000000000000000000000000000000000000000000000000),((15832915831765731:ℚ)/243200000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((1929734643:ℚ)/2500000000),((4114061041:ℚ)/5000000000),((-11062183123:ℚ)/30500000000),((-547244881:ℚ)/2160000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((31737231115728416009727395744401493993839950024219877:ℚ)/1280707200000000000000000000000000000000000000000000000),((8258959:ℚ)/128000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((2048573571:ℚ)/2500000000),((10129429701:ℚ)/10000000000),((-27828289103:ℚ)/64800000000),((-1760573571:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((7239086690758874985122239820894514572229383476809867601:ℚ)/259200000000000000000000000000000000000000000000000000000),((8258959:ℚ)/128000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((1009537893:ℚ)/1000000000),((6965482043:ℚ)/5000000000),((-19616446129:ℚ)/40000000000),((-298112631:ℚ)/1472000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((157679285698014170337913452133190690954862474641981:ℚ)/4983603200000000000000000000000000000000000000000000),((8258959:ℚ)/128000000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC11
#check @N11Formalization.C450TenthGroupedC11.bound
#print axioms N11Formalization.C450TenthGroupedC11.valid0
#print axioms N11Formalization.C450TenthGroupedC11.valid1
#print axioms N11Formalization.C450TenthGroupedC11.valid2
#print axioms N11Formalization.C450TenthGroupedC11.valid3
#print axioms N11Formalization.C450TenthGroupedC11.valid4
#print axioms N11Formalization.C450TenthGroupedC11.valid5
#print axioms N11Formalization.C450TenthGroupedC11.valid6
#print axioms N11Formalization.C450TenthGroupedC11.valid7
#print axioms N11Formalization.C450TenthGroupedC11.valid8
#print axioms N11Formalization.C450TenthGroupedC11.valid9
#print axioms N11Formalization.C450TenthGroupedC11.valid10
#print axioms N11Formalization.C450TenthGroupedC11.valid11
#print axioms N11Formalization.C450TenthGroupedC11.valid12
#print axioms N11Formalization.C450TenthGroupedC11.valid13
#print axioms N11Formalization.C450TenthGroupedC11.valid14
#print axioms N11Formalization.C450TenthGroupedC11.valid15
#print axioms N11Formalization.C450TenthGroupedC11.valid16
#print axioms N11Formalization.C450TenthGroupedC11.valid17
#print axioms N11Formalization.C450TenthGroupedC11.bound
#print axioms N11Formalization.C450TenthGroupedC11.endpoint_checks
