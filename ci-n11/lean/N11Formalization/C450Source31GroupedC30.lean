import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((13:ℚ)/16),((7:ℚ)/8),((5122722249:ℚ)/10000000000),((2729691757:ℚ)/5000000000),((85155389237:ℚ)/103000000000),((23907842299:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1662257471:ℚ)/2000000000),((-8601765126517965026075375722756266260989291:ℚ)/25284217520000000000000000000000000000000000),((-1811478941145809857435798791:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((335077051:ℚ)/625000000),((1424539361:ℚ)/2500000000),((1838667221:ℚ)/2225000000),((12371775527:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((246179131:ℚ)/312500000),((-141408606143964008682751937358154894504482756459524066741:ℚ)/412725952482223510742187500000000000000000000000000000000),((-445769391375181129278165039:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((2799835521:ℚ)/5000000000),((23270043:ℚ)/40000000),((45677861773:ℚ)/54350000000),((67096767:ℚ)/71200000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3712364757:ℚ)/5000000000),((-955478871293531074692250898861245915854095456719098461:ℚ)/2665502452355200000000000000000000000000000000000000000),((-113200225807445813091991:ℚ)/236584960000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((5718865417:ℚ)/10000000000),((742105397:ℚ)/1250000000),((92905250421:ℚ)/110600000000),((6394737779:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3594866739:ℚ)/5000000000),((-960557296387379290450022118633096915791284648851202576233:ℚ)/2675536905744600296020507812500000000000000000000000000000),((-109646695816201509143827831:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((5838044441:ℚ)/10000000000),((6056155789:ℚ)/10000000000),((94454577733:ℚ)/112500000000),((51993090523:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3474140739:ℚ)/5000000000),((-69795400273824323248963996754389082238736329484990050409:ℚ)/194134106250000000000000000000000000000000000000000000000),((-6959433178183050487050512839:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((5957208897:ℚ)/10000000000),((6115804979:ℚ)/10000000000),((96003715661:ℚ)/113450000000),((52410634853:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6699651999:ℚ)/10000000000),((-25903222646542413927476172929425096860725110331511215276613319:ℚ)/70701979064941406250000000000000000000000000000000000000000000),((-6930331735873619623353442119:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6016785893:ℚ)/10000000000),((385965599:ℚ)/625000000),((96778216609:ℚ)/114400000000),((3301759193:ℚ)/3545312500),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6572384757:ℚ)/10000000000),((-42749856196579994506658815440849797950951576651332892124177:ℚ)/116639489525361816406250000000000000000000000000000000000000),((-26957608329231153166861359:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6076359517:ℚ)/10000000000),((6235089719:ℚ)/10000000000),((32517557907:ℚ)/38450000000),((4095817541:ℚ)/4400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3221495181:ℚ)/5000000000),((-28858780188534929028090335751845561843598235607004005234823:ℚ)/78710149100000000000000000000000000000000000000000000000000),((-6871881130452256194523136799:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6135929853:ℚ)/10000000000),((3147362747:ℚ)/5000000000),((98327088089:ℚ)/116300000000),((26831539229:ℚ)/28837500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6311335047:ℚ)/10000000000),((-110155371197484788318630662267138935567437626920438678274709:ℚ)/300336763612559082031250000000000000000000000000000000000000),((-1710632973807572394483113431:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((6195496983:ℚ)/10000000000),((1270871403:ℚ)/2000000000),((99101460779:ℚ)/117250000000),((10816099821:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((6177271289:ℚ)/10000000000),((-198355439579881034187266086886914557721213905394236414953767:ℚ)/540635868543542187500000000000000000000000000000000000000000),((-272523999712678872648495031:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((781882623:ℚ)/1250000000),((6413984387:ℚ)/10000000000),((12484474099:ℚ)/14775000000),((54497890709:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((755079469:ℚ)/1250000000),((-1921755266230934249512708825896287944261142366419792453259363:ℚ)/5236296863552856445312500000000000000000000000000000000000000),((-6783585389303722562847815271:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6314621933:ℚ)/10000000000),((6473607709:ℚ)/10000000000),((100650085129:ℚ)/119150000000),((54915253963:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5901246777:ℚ)/10000000000),((-99615742873719369836878710813932803724078393050879626547351187:ℚ)/271348097224981250000000000000000000000000000000000000000000000),((-6753988053166476290832202279:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6374179903:ℚ)/10000000000),((3266613539:ℚ)/5000000000),((101424338739:ℚ)/120100000000),((27666294773:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5758901383:ℚ)/10000000000),((-5468521519869910856390269926919450179295260531646807084114071:ℚ)/14891834997348546600341796875000000000000000000000000000000000),((-1681076988328567216837340839:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((1286746993:ℚ)/2000000000),((6592842589:ℚ)/10000000000),((20439710909:ℚ)/24210000000),((55749898123:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2806685787:ℚ)/5000000000),((-323744038637398791908371191844013941856428532046088653917743969:ℚ)/881385947521600781250000000000000000000000000000000000000000000),((-6694545059103541719450966439:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((1623321797:ℚ)/2500000000),((6652454331:ℚ)/10000000000),((25743183361:ℚ)/30500000000),((6240797813:ℚ)/6725000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1092879959:ℚ)/2000000000),((-2598722350815803488698857885119920210861974169491527619191:ℚ)/7073210018457031250000000000000000000000000000000000000000),((-6664699342357956433252554199:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid source31 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source31 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6552836639:ℚ)/10000000000),((338583343:ℚ)/500000000),((103746876307:ℚ)/123900000000),((2850083401:ℚ)/3050000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1327923317:ℚ)/2500000000),((-2735670503630618907471609061630493890257989170254137282307:ℚ)/7561703552539062500000000000000000000000000000000000000000),((-16511898320098701187066191:ℚ)/36966400000000000000000000)⟩
theorem valid15 : Valid source31 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6671927481:ℚ)/10000000000),((6890865339:ℚ)/10000000000),((105295057253:ℚ)/125800000000),((19278685791:ℚ)/20650000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4993683943:ℚ)/10000000000),((-1099803018870024137269658030843420788348894647194473230701:ℚ)/3037690196236419677734375000000000000000000000000000000000),((-6544487694114624510133524439:ℚ)/14786560000000000000000000000)⟩
theorem valid16 : Valid source31 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source31 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((424437999:ℚ)/625000000),((1425844527:ℚ)/2000000000),((6677693987:ℚ)/8100000000),((11900911689:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((931194071:ℚ)/2000000000),((-9561146010800461456322321567339656708762045678254966563681:ℚ)/27212642967150000000000000000000000000000000000000000000000),((-256917950829987604858520911:ℚ)/591462400000000000000000000)⟩
theorem valid17 : Valid source31 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source31 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((7029139803:ℚ)/10000000000),((808219979:ℚ)/1000000000),((109938817439:ℚ)/144800000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((3900585031:ℚ)/10000000000),((-31222039415366225204552666441149309469:ℚ)/104835200000000000000000000000000000000),((-427903021:ℚ)/1024000000)⟩
theorem valid18 : Valid source31 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((399066717:ℚ)/500000000),((1806921823:ℚ)/2000000000),((6115867321:ℚ)/8000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-96386381197191888472963255445487709:ℚ)/320000000000000000000000000000000000),((-427903021:ℚ)/1024000000)⟩
theorem valid19 : Valid source31 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source31 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((1786622147:ℚ)/2000000000),((1284092143:ℚ)/1000000000),((8979362637:ℚ)/14720000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-23086587036111940233492921:ℚ)/108339200000000000000000000),((-427903021:ℚ)/1024000000)⟩
theorem valid20 : Valid source31 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source31 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source31 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source31 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source31 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source31 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC30
#check @N11Formalization.C450Source31GroupedC30.bound
#print axioms N11Formalization.C450Source31GroupedC30.valid0
#print axioms N11Formalization.C450Source31GroupedC30.valid1
#print axioms N11Formalization.C450Source31GroupedC30.valid2
#print axioms N11Formalization.C450Source31GroupedC30.valid3
#print axioms N11Formalization.C450Source31GroupedC30.valid4
#print axioms N11Formalization.C450Source31GroupedC30.valid5
#print axioms N11Formalization.C450Source31GroupedC30.valid6
#print axioms N11Formalization.C450Source31GroupedC30.valid7
#print axioms N11Formalization.C450Source31GroupedC30.valid8
#print axioms N11Formalization.C450Source31GroupedC30.valid9
#print axioms N11Formalization.C450Source31GroupedC30.valid10
#print axioms N11Formalization.C450Source31GroupedC30.valid11
#print axioms N11Formalization.C450Source31GroupedC30.valid12
#print axioms N11Formalization.C450Source31GroupedC30.valid13
#print axioms N11Formalization.C450Source31GroupedC30.valid14
#print axioms N11Formalization.C450Source31GroupedC30.valid15
#print axioms N11Formalization.C450Source31GroupedC30.valid16
#print axioms N11Formalization.C450Source31GroupedC30.valid17
#print axioms N11Formalization.C450Source31GroupedC30.valid18
#print axioms N11Formalization.C450Source31GroupedC30.valid19
#print axioms N11Formalization.C450Source31GroupedC30.valid20
#print axioms N11Formalization.C450Source31GroupedC30.bound
#print axioms N11Formalization.C450Source31GroupedC30.endpoint_checks
