import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((6171768727:ℚ)/10000000000),((3334562379:ℚ)/5000000000),((56:ℚ)/1335),((5894562379:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((778871803:ℚ)/1250000000),((41190173851134797706092607651835679820719:ℚ)/2174741093376000000000000000000000000000000),((-178173441039629:ℚ)/5120000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((664735517:ℚ)/1000000000),((6787977541:ℚ)/10000000000),((224:ℚ)/5435),((3969325847:ℚ)/35600000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5060788781:ℚ)/10000000000),((18233270637326003596188902624766042483078592416822841256032427:ℚ)/999563419633200000000000000000000000000000000000000000000000000),((-364616072636221:ℚ)/9728000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((3383119473:ℚ)/5000000000),((1726706697:ℚ)/2500000000),((16:ℚ)/395),((3006706697:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((94560929:ℚ)/200000000),((2660709816980490845064987396892841556603205801464061753997:ℚ)/146772310257989501953125000000000000000000000000000000000000),((-1855685011493649:ℚ)/48640000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((6885118117:ℚ)/10000000000),((7025672679:ℚ)/10000000000),((224:ℚ)/5625),((1735096097:ℚ)/15800000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((874419609:ℚ)/2000000000),((35990798608238391775947760397456406014657358363165700679:ℚ)/1996807950000000000000000000000000000000000000000000000000),((-3776576793710021:ℚ)/97280000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((7003992919:ℚ)/10000000000),((7085094419:ℚ)/10000000000),((448:ℚ)/11345),((12205094419:ℚ)/112500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((49833779:ℚ)/125000000),((820516617210784690484159366446570295997355441146216803002514357:ℚ)/45814882434082031250000000000000000000000000000000000000000000000),((-3841781167979447:ℚ)/97280000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((5650743:ℚ)/8000000),((7144515381:ℚ)/10000000000),((28:ℚ)/715),((12264515381:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1890082627:ℚ)/5000000000),((10258572586444906016532717446255747415886914890649928321319:ℚ)/574225179201781250000000000000000000000000000000000000000000),((-3099505995159:ℚ)/77824000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((7122863569:ℚ)/10000000000),((3601967793:ℚ)/5000000000),((448:ℚ)/11535),((6161967793:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((712456289:ℚ)/2000000000),((9246038963489888688480152715114883003238479756423607709240797:ℚ)/518778592718100000000000000000000000000000000000000000000000000),((-3906983264822897:ℚ)/97280000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7182297401:ℚ)/10000000000),((7263355051:ℚ)/10000000000),((224:ℚ)/5815),((4127785017:ℚ)/38450000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((666164121:ℚ)/2000000000),((341802455471123416923002398160657762462070252227836471355359:ℚ)/19221552871203781250000000000000000000000000000000000000000000),((-3939583494314713:ℚ)/97280000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),(0:ℚ),((1:ℚ)/16),((7241730271:ℚ)/10000000000),((1464554759:ℚ)/2000000000),((64:ℚ)/1675),((2488554759:ℚ)/23260000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1541360709:ℚ)/5000000000),((1566179714884031190006260486301590645665030537067458298193:ℚ)/88267080578537500000000000000000000000000000000000000000000),((-3972183196137023:ℚ)/97280000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7301162201:ℚ)/10000000000),((1476438367:ℚ)/2000000000),((112:ℚ)/2955),((357205481:ℚ)/3350000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1406790439:ℚ)/5000000000),((363304269614079212004551301989147315660039517659796497663:ℚ)/20517734649023437500000000000000000000000000000000000000000),((-4004782382357113:ℚ)/97280000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((115009269:ℚ)/156250000),((750102587:ℚ)/1000000000),((224:ℚ)/6005),((1262102587:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1258325883:ℚ)/5000000000),((790049104418188840163019942216384689821484374167283748997103:ℚ)/44662159325320650000000000000000000000000000000000000000000000),((-63084079166997:ℚ)/1520000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((3739726291:ℚ)/5000000000),((1523971457:ℚ)/2000000000),((56:ℚ)/1525),((2547971457:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1783457983:ℚ)/10000000000),((5680165966958448436320181170803514320956974431995827554431:ℚ)/322298805966050000000000000000000000000000000000000000000000),((-2051288487055283:ℚ)/48640000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7598308537:ℚ)/10000000000),((161903181:ℚ)/200000000),((14:ℚ)/405),((264303181:ℚ)/2440000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((13186439:ℚ)/625000000),((2630240159711397759840636352868774069776747298950211467:ℚ)/148922234100000000000000000000000000000000000000000000000),((-4167771010555481:ℚ)/97280000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((2018425313:ℚ)/2500000000),((4998039617:ℚ)/5000000000),((7:ℚ)/250),((2519346539:ℚ)/21600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((210080570282694723227951661104783554240650768221274431:ℚ)/11809800000000000000000000000000000000000000000000000000),((-548513:ℚ)/12800000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((1246862337:ℚ)/1250000000),((1379715913:ℚ)/1000000000),((7:ℚ)/345),((1891715913:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((95773397580910010333961656249339663213:ℚ)/4875264000000000000000000000000000000000),((-548513:ℚ)/12800000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC17
#check @N11Formalization.C450NinthGroupedC17.bound
#print axioms N11Formalization.C450NinthGroupedC17.valid0
#print axioms N11Formalization.C450NinthGroupedC17.valid1
#print axioms N11Formalization.C450NinthGroupedC17.valid2
#print axioms N11Formalization.C450NinthGroupedC17.valid3
#print axioms N11Formalization.C450NinthGroupedC17.valid4
#print axioms N11Formalization.C450NinthGroupedC17.valid5
#print axioms N11Formalization.C450NinthGroupedC17.valid6
#print axioms N11Formalization.C450NinthGroupedC17.valid7
#print axioms N11Formalization.C450NinthGroupedC17.valid8
#print axioms N11Formalization.C450NinthGroupedC17.valid9
#print axioms N11Formalization.C450NinthGroupedC17.valid10
#print axioms N11Formalization.C450NinthGroupedC17.valid11
#print axioms N11Formalization.C450NinthGroupedC17.valid12
#print axioms N11Formalization.C450NinthGroupedC17.valid13
#print axioms N11Formalization.C450NinthGroupedC17.valid14
#print axioms N11Formalization.C450NinthGroupedC17.bound
#print axioms N11Formalization.C450NinthGroupedC17.endpoint_checks
