import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((6243496983:ℚ)/10000000000),((3259477989:ℚ)/5000000000),((-5618433967:ℚ)/49600000000),((-1763496983:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((24269491:ℚ)/40000000),((1330928169080500933606290001884480886588418924533836114503:ℚ)/26464482031250000000000000000000000000000000000000000000000),((-38306497476749831698185829:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((1620448227:ℚ)/2500000000),((3378648299:ℚ)/5000000000),((-5975944897:ℚ)/51500000000),((-500448227:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5493434899:ℚ)/10000000000),((6355545273924023269551715013647270042464816374117374577:ℚ)/127637941992187500000000000000000000000000000000000000000),((-2834154268669017987393469:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((840003991:ℚ)/1250000000),((6876444757:ℚ)/10000000000),((-12309334271:ℚ)/106800000000),((-280003991:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((971972473:ℚ)/2000000000),((25675067531567866242366251686014996475550234971188764683:ℚ)/523262923127746582031250000000000000000000000000000000000),((-818575457014059064412741:ℚ)/28880000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((854891497:ℚ)/1250000000),((6995579169:ℚ)/10000000000),((-12666737507:ℚ)/108700000000),((-294891497:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2256443827:ℚ)/5000000000),((1714027631389421725121652228915709295797640902018361561:ℚ)/35061865577507019042968750000000000000000000000000000000),((-873608759967191885583749:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((1391643989:ℚ)/2000000000),((7055141441:ℚ)/10000000000),((-12845424323:ℚ)/110600000000),((-495643989:ℚ)/11155000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((82781999:ℚ)/200000000),((14563859807427447221369998168313886690296029378253868547:ℚ)/299842983018701171875000000000000000000000000000000000000),((-2377350081003413399691181:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((1403551919:ℚ)/2000000000),((889337567:ℚ)/1250000000),((-1628012701:ℚ)/13943750000),((-169183973:ℚ)/3750000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3939778331:ℚ)/10000000000),((15477112356720973522485258628301285477978489658980717:ℚ)/319147109985351562500000000000000000000000000000000000),((-2447816035800633399220021:ℚ)/73932800000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((1769324113:ℚ)/2500000000),((7174256533:ℚ)/10000000000),((-13202769599:ℚ)/112500000000),((-649324113:ℚ)/14181250000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1865207011:ℚ)/5000000000),((19420102490951691763216592262641266020250030329726983:ℚ)/401056976245880126953125000000000000000000000000000000),((-3934826335036739938773109:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7136830587:ℚ)/10000000000),((723380951:ℚ)/1000000000),((-1338142853:ℚ)/11345000000),((-2656830587:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1754602811:ℚ)/5000000000),((128328662193039484044569193938481837030143975158915895360633:ℚ)/2654010273200000000000000000000000000000000000000000000000000),((-64719215487515819136208909:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((7196362069:ℚ)/10000000000),((7293359543:ℚ)/10000000000),((-13560078629:ℚ)/114400000000),((-905454023:ℚ)/19225000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3273748453:ℚ)/10000000000),((11978439737078800525234736709289030180452475447361471:ℚ)/248070507381439208984375000000000000000000000000000000),((-66481385283522979354850221:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((1813972741:ℚ)/2500000000),((1470581341:ℚ)/2000000000),((-2747744023:ℚ)/23070000000),((-693972741:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3020707421:ℚ)/10000000000),((2136257677528229759393537039269113403913207839558337632697:ℚ)/44299292997180175781250000000000000000000000000000000000000),((-4265233291793211379537741:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((1463083467:ℚ)/2000000000),((7471992689:ℚ)/10000000000),((-14095978067:ℚ)/116300000000),((-567083467:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1372609533:ℚ)/5000000000),((5368712603391416416334909691612561864637001404642834133:ℚ)/111144609987500000000000000000000000000000000000000000000),((-7756926257661803679589:ℚ)/204800000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7434462749:ℚ)/10000000000),((7710133137:ℚ)/10000000000),((-14810399411:ℚ)/118200000000),((-2954462749:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2090968677:ℚ)/10000000000),((40632865607600319727202585509557676724820578982670743079661:ℚ)/838411068750000000000000000000000000000000000000000000000000),((-73531858451359000091492861:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7672525877:ℚ)/10000000000),((163726019:ℚ)/200000000),((-324778057:ℚ)/2440000000),((-3192525877:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((187426235450205745548740908626596165886299707438829234141:ℚ)/3842121600000000000000000000000000000000000000000000000000),((-2715929:ℚ)/64000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((1018569093:ℚ)/1250000000),((10089859791:ℚ)/10000000000),((-21949579373:ℚ)/129600000000),((-458569093:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((25940826556101346411811064236659911962355070521167411203:ℚ)/506250000000000000000000000000000000000000000000000000000),((-2715929:ℚ)/64000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((502584119:ℚ)/500000000),((6947016391:ℚ)/5000000000),((-16681049173:ℚ)/80000000000),((-4037451:ℚ)/80000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((45433088262965843096843951459491517404883598229:ℚ)/800000000000000000000000000000000000000000000000),((-2715929:ℚ)/64000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC14
#check @N11Formalization.C450Source15GroupedC14.bound
#print axioms N11Formalization.C450Source15GroupedC14.valid0
#print axioms N11Formalization.C450Source15GroupedC14.valid1
#print axioms N11Formalization.C450Source15GroupedC14.valid2
#print axioms N11Formalization.C450Source15GroupedC14.valid3
#print axioms N11Formalization.C450Source15GroupedC14.valid4
#print axioms N11Formalization.C450Source15GroupedC14.valid5
#print axioms N11Formalization.C450Source15GroupedC14.valid6
#print axioms N11Formalization.C450Source15GroupedC14.valid7
#print axioms N11Formalization.C450Source15GroupedC14.valid8
#print axioms N11Formalization.C450Source15GroupedC14.valid9
#print axioms N11Formalization.C450Source15GroupedC14.valid10
#print axioms N11Formalization.C450Source15GroupedC14.valid11
#print axioms N11Formalization.C450Source15GroupedC14.valid12
#print axioms N11Formalization.C450Source15GroupedC14.valid13
#print axioms N11Formalization.C450Source15GroupedC14.valid14
#print axioms N11Formalization.C450Source15GroupedC14.bound
#print axioms N11Formalization.C450Source15GroupedC14.endpoint_checks
