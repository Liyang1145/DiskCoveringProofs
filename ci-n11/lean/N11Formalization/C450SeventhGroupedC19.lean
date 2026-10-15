import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((3075258261:ℚ)/5000000000),((830881239:ℚ)/1250000000),((3875258261:ℚ)/26700000000),((2972643717:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3139367561:ℚ)/5000000000),((144256238131193227731395572275859577489:ℚ)/16990164792000000000000000000000000000000),((-6829921043423811985092811:ℚ)/173280000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6625835777:ℚ)/10000000000),((3442325657:ℚ)/5000000000),((8225835777:ℚ)/55300000000),((4082325657:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1279723967:ℚ)/2500000000),((43059404731951948784696738015131751051601540562619990328087:ℚ)/5389646623025000000000000000000000000000000000000000000000000),((-9431775616542902544710513:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((857934867:ℚ)/1250000000),((1400689889:ℚ)/2000000000),((1057934867:ℚ)/7031250000),((4970069667:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2219433513:ℚ)/5000000000),((3046104481442903084299279867271755132362755678011864651:ℚ)/391374358200000000000000000000000000000000000000000000000),((-449767641937719628042399:ℚ)/10830000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((3491148443:ℚ)/5000000000),((1412569581:ℚ)/2000000000),((4291148443:ℚ)/28362500000),((1668569581:ℚ)/7500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((162384447:ℚ)/400000000),((52192136379520746319444018660478314344966316461059801253499:ℚ)/6787389990234375000000000000000000000000000000000000000000000),((-2419210529305140845964953:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((7041705007:ℚ)/10000000000),((890280747:ℚ)/1250000000),((664746539:ℚ)/4400000000),((3150842241:ℚ)/14181250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1928435963:ℚ)/5000000000),((60103147256793668965370542578852495105576797617463103:ℚ)/7842891979919433593750000000000000000000000000000000000),((-26919066596964498879273:ℚ)/640000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((7101112577:ℚ)/10000000000),((3590821833:ℚ)/5000000000),((2900370859:ℚ)/19225000000),((12692465499:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3643462477:ℚ)/10000000000),((660435290667580707928474073350769265925885964271068086236349:ℚ)/86463098786350000000000000000000000000000000000000000000000000),((-9758751563813062584108913:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((716051961:ℚ)/1000000000),((1448208197:ℚ)/2000000000),((876051961:ℚ)/5815000000),((1704208197:ℚ)/7690000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((106793133:ℚ)/312500000),((585443570307390631346479163938076295520736629978349464027:ℚ)/76886211484815125000000000000000000000000000000000000000000),((-293992430790998072940211:ℚ)/6931200000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/8),((3:ℚ)/16),((180498153:ℚ)/250000000),((7300437943:ℚ)/10000000000),((220498153:ℚ)/1465625000),((25741313829:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((793978901:ℚ)/2500000000),((2052135328757201119409202760966958493545403989799764158369691:ℚ)/270317934271771093750000000000000000000000000000000000000000000),((-18451446446394850251919:ℚ)/433200000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((3639666059:ℚ)/5000000000),((7359834547:ℚ)/10000000000),((4439666059:ℚ)/29550000000),((25919503641:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2915243971:ℚ)/10000000000),((3329550198043853664514507189802202043327068158940852234877279:ℚ)/439848936538439941406250000000000000000000000000000000000000000),((-2470455701452511513516857:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((3669368809:ℚ)/5000000000),((7419230807:ℚ)/10000000000),((4469368809:ℚ)/29787500000),((8699230807:ℚ)/39400000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1314827247:ℚ)/5000000000),((24580807662943219824570959595225518719152283328170393143292211:ℚ)/3256177166699775000000000000000000000000000000000000000000000000),((-2480725451298153939655857:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((7398142631:ℚ)/10000000000),((747862673:ℚ)/1000000000),((8998142631:ℚ)/60050000000),((2627588019:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1154958743:ℚ)/5000000000),((3587951380936533277831538683908029183574762133109180868509:ℚ)/476538719915153491210937500000000000000000000000000000000000),((-9964008443135685400598817:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7457547169:ℚ)/10000000000),((3798708799:ℚ)/5000000000),((9057547169:ℚ)/61000000000),((13316126397:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((969604121:ℚ)/5000000000),((18995529348281103472485428284315650576692924421386506481163:ℚ)/2517959421609765625000000000000000000000000000000000000000000),((-10005142727263383077181617:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((473522179:ℚ)/625000000),((4036284541:ℚ)/5000000000),((573522179:ℚ)/4050000000),((14028853623:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((157805367:ℚ)/2000000000),((8955652831241906197385850801350937344291148528946160447497:ℚ)/1163454953906250000000000000000000000000000000000000000000000),((-39404274460577107223927:ℚ)/902500000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((1610313743:ℚ)/2000000000),((9973031059:ℚ)/10000000000),((1930313743:ℚ)/16000000000),((3751010353:ℚ)/14400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((14294936879042408053568069276763842390826632939635589:ℚ)/1749600000000000000000000000000000000000000000000000000),((-5597727:ℚ)/128000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9952220861:ℚ)/10000000000),((6886786649:ℚ)/5000000000),((3850740287:ℚ)/36800000000),((22580359947:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((324791527961493276580748199053434045959:ℚ)/33856000000000000000000000000000000000000),((-5597727:ℚ)/128000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC19
#check @N11Formalization.C450SeventhGroupedC19.bound
#print axioms N11Formalization.C450SeventhGroupedC19.valid0
#print axioms N11Formalization.C450SeventhGroupedC19.valid1
#print axioms N11Formalization.C450SeventhGroupedC19.valid2
#print axioms N11Formalization.C450SeventhGroupedC19.valid3
#print axioms N11Formalization.C450SeventhGroupedC19.valid4
#print axioms N11Formalization.C450SeventhGroupedC19.valid5
#print axioms N11Formalization.C450SeventhGroupedC19.valid6
#print axioms N11Formalization.C450SeventhGroupedC19.valid7
#print axioms N11Formalization.C450SeventhGroupedC19.valid8
#print axioms N11Formalization.C450SeventhGroupedC19.valid9
#print axioms N11Formalization.C450SeventhGroupedC19.valid10
#print axioms N11Formalization.C450SeventhGroupedC19.valid11
#print axioms N11Formalization.C450SeventhGroupedC19.valid12
#print axioms N11Formalization.C450SeventhGroupedC19.valid13
#print axioms N11Formalization.C450SeventhGroupedC19.valid14
#print axioms N11Formalization.C450SeventhGroupedC19.bound
#print axioms N11Formalization.C450SeventhGroupedC19.endpoint_checks
