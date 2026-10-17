import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((6246396691:ℚ)/10000000000),((6510039369:ℚ)/10000000000),((-5390039369:ℚ)/24800000000),((-13619190073:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((303033903:ℚ)/500000000),((13881591044166637517771315566524258672063587523305536650557:ℚ)/635147568750000000000000000000000000000000000000000000000000),((1051671334145855429742641:ℚ)/36480000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6484122071:ℚ)/10000000000),((3373902557:ℚ)/5000000000),((-2813902557:ℚ)/12875000000),((-14332366213:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1097512493:ℚ)/2000000000),((4250200339131094790790021642782935305909067502666639271587:ℚ)/196051878900000000000000000000000000000000000000000000000000),((1606834477331065251342937:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((210057231:ℚ)/312500000),((6866681007:ℚ)/10000000000),((-5746681007:ℚ)/26700000000),((-470171693:ℚ)/3396875000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((19419163:ℚ)/40000000),((464329041577824376594512453264978106427087070647610461:ℚ)/21802621796989440917968750000000000000000000000000000000),((18524135590106522727285011:ℚ)/693120000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((6840680557:ℚ)/10000000000),((6985552569:ℚ)/10000000000),((-5865552569:ℚ)/27175000000),((-15402041671:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((563526667:ℚ)/1250000000),((9148543909147760841374212322475938120047681569649884283043:ℚ)/430840204216406250000000000000000000000000000000000000000000),((18176986321860590978432579:ℚ)/693120000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((6959526311:ℚ)/10000000000),((1408997359:ℚ)/2000000000),((-169285337:ℚ)/790000000),((-15758578933:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((826964807:ℚ)/2000000000),((902329172048969557593508572539584183682518587865207093699:ℚ)/42834711859814453125000000000000000000000000000000000000000),((237320189014897319336753:ℚ)/9241600000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((1754736991:ℚ)/2500000000),((7104420019:ℚ)/10000000000),((-5984420019:ℚ)/27887500000),((-3984210973:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((983925727:ℚ)/2500000000),((76484223373945290001579459323444004846982515202530980577:ℚ)/3635285049676895141601562500000000000000000000000000000000),((5875372790710008682711993:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((7078368827:ℚ)/10000000000),((3581926133:ℚ)/5000000000),((-1007308711:ℚ)/4687500000),((-16115106481:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((465817557:ℚ)/1250000000),((479459467227826433119699219321417660139221681054657833:ℚ)/22815685759765625000000000000000000000000000000000000000),((1454457732027114937275657:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-1:ℚ)/4),((-3:ℚ)/16),((3568894461:ℚ)/5000000000),((7193568031:ℚ)/10000000000),((-6073568031:ℚ)/28362500000),((-8146683383:ℚ)/56962500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3505535647:ℚ)/10000000000),((18292353663070868396893020616296668836714182471051694546153:ℚ)/873696072169665527343750000000000000000000000000000000000000),((5754961367787860035427793:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((7167498687:ℚ)/10000000000),((7223283561:ℚ)/10000000000),((-6103283561:ℚ)/28481250000),((-16382496061:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1694936079:ℚ)/5000000000),((297434614682461469346012139011384140000173321023738639934723:ℚ)/14213985385600000000000000000000000000000000000000000000000000),((47586539585278766105579:ℚ)/1920000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((7197208267:ℚ)/10000000000),((910339241:ℚ)/1250000000),((-770339241:ℚ)/3575000000),((-16471624801:ℚ)/115350000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((817571029:ℚ)/2500000000),((3370533492900433737032715486233194141197577089689019517:ℚ)/160749688783172607421875000000000000000000000000000000000),((89109645674945838502353:ℚ)/3610000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((22676959:ℚ)/31250000),((7342143389:ℚ)/10000000000),((-6222143389:ℚ)/28837500000),((-52030877:ℚ)/363437500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3017450871:ℚ)/10000000000),((4832682264351808476118578875145242837836066443852081:ℚ)/230725484360313415527343750000000000000000000000000000),((5645745539555800193824473:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((365802239:ℚ)/500000000),((3700785983:ℚ)/5000000000),((-3140785983:ℚ)/14537500000),((-841406717:ℚ)/5862500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((171385747:ℚ)/625000000),((91935907981385430193049793148167999072383611127568509021:ℚ)/4393691439221191406250000000000000000000000000000000000000),((1397140934934277457709457:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1475092397:ℚ)/2000000000),((7460999681:ℚ)/10000000000),((-6340999681:ℚ)/29312500000),((-3401277191:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((304605853:ℚ)/1250000000),((67460708700286744911532253386030981343924877571432676561:ℚ)/3227111943300000000000000000000000000000000000000000000000),((5531471903226439019570193:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((743487851:ℚ)/1000000000),((1515970521:ℚ)/2000000000),((-1291970521:ℚ)/5910000000),((-1718463553:ℚ)/12010000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((417666321:ℚ)/2000000000),((33570080475993349399742415432819926692607299169521391239:ℚ)/1599692575298437500000000000000000000000000000000000000000),((658298183929400633060099:ℚ)/27724800000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((7553709587:ℚ)/10000000000),((96233779:ℚ)/125000000),((-82233779:ℚ)/375312500),((-17541128761:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1104267809:ℚ)/10000000000),((856534248665168828363959899101926319864402555311972440404891:ℚ)/40890627150000000000000000000000000000000000000000000000000000),((140872798056229:ℚ)/6080000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((7672538137:ℚ)/10000000000),((8174071907:ℚ)/10000000000),((-7054071907:ℚ)/30500000000),((-17897614411:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5938038357265527274963573032804358803193445544759911879549:ℚ)/276632755200000000000000000000000000000000000000000000000000),((73407:ℚ)/3200000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((2036957321:ℚ)/2500000000),((201503977:ℚ)/200000000),((-179103977:ℚ)/648000000),((-4830871963:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((249907551493112150029980115659893579302883376505561105913:ℚ)/10800000000000000000000000000000000000000000000000000000000),((73407:ℚ)/3200000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((5024358547:ℚ)/5000000000),((13876521303:ℚ)/10000000000),((-12756521303:ℚ)/40000000000),((-544046767:ℚ)/4800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((13363407701753883450076339713369658265641725354006893:ℚ)/518400000000000000000000000000000000000000000000000000),((73407:ℚ)/3200000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC13
#check @N11Formalization.C450NinthGroupedC13.bound
#print axioms N11Formalization.C450NinthGroupedC13.valid0
#print axioms N11Formalization.C450NinthGroupedC13.valid1
#print axioms N11Formalization.C450NinthGroupedC13.valid2
#print axioms N11Formalization.C450NinthGroupedC13.valid3
#print axioms N11Formalization.C450NinthGroupedC13.valid4
#print axioms N11Formalization.C450NinthGroupedC13.valid5
#print axioms N11Formalization.C450NinthGroupedC13.valid6
#print axioms N11Formalization.C450NinthGroupedC13.valid7
#print axioms N11Formalization.C450NinthGroupedC13.valid8
#print axioms N11Formalization.C450NinthGroupedC13.valid9
#print axioms N11Formalization.C450NinthGroupedC13.valid10
#print axioms N11Formalization.C450NinthGroupedC13.valid11
#print axioms N11Formalization.C450NinthGroupedC13.valid12
#print axioms N11Formalization.C450NinthGroupedC13.valid13
#print axioms N11Formalization.C450NinthGroupedC13.valid14
#print axioms N11Formalization.C450NinthGroupedC13.valid15
#print axioms N11Formalization.C450NinthGroupedC13.valid16
#print axioms N11Formalization.C450NinthGroupedC13.valid17
#print axioms N11Formalization.C450NinthGroupedC13.bound
#print axioms N11Formalization.C450NinthGroupedC13.endpoint_checks
