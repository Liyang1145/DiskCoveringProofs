import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((3123487533:ℚ)/5000000000),((6508461843:ℚ)/10000000000),((-5868461843:ℚ)/19840000000),((-2643487533:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1211868393:ℚ)/2000000000),((2335222251830339250440644126991618540647194193792750787:ℚ)/206753765869140625000000000000000000000000000000000000000),((46141917641359087465376899:ℚ)/1108992000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6484586717:ℚ)/10000000000),((843263201:ℚ)/1250000000),((-763263201:ℚ)/2575000000),((-5524586717:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1097278059:ℚ)/2000000000),((17188725908530150963204345054402561088710567601609867339:ℚ)/1531655303906250000000000000000000000000000000000000000000),((237758126193766553423717:ℚ)/5776000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6722190417:ℚ)/10000000000),((3432461859:ℚ)/5000000000),((-3112461859:ℚ)/10680000000),((-5762190417:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4853778289:ℚ)/10000000000),((184128946271928366761906422016722072245695536501413649771:ℚ)/16744413540087890625000000000000000000000000000000000000000),((11273117164390423235708131:ℚ)/277248000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((6840989547:ℚ)/10000000000),((3491869743:ℚ)/5000000000),((-3171869743:ℚ)/10870000000),((-5880989547:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1126820031:ℚ)/2500000000),((12310454143684713093011925541001258695462209931176381269:ℚ)/1121979698480224609375000000000000000000000000000000000000),((11212321640589603869456299:ℚ)/277248000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1739946747:ℚ)/2500000000),((7043146529:ℚ)/10000000000),((-6403146529:ℚ)/22120000000),((-1499946747:ℚ)/6971875000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((826794061:ℚ)/2000000000),((397896620128638890083918742425612035917881966308782171:ℚ)/36601926638025045394897460937500000000000000000000000000),((14857265009351686413676697:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((3509592551:ℚ)/5000000000),((7102553031:ℚ)/10000000000),((-6462553031:ℚ)/22310000000),((-3029592551:ℚ)/14062500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1967444591:ℚ)/5000000000),((2467724689664789992448101655000331593006539402521793483:ℚ)/227205315604805946350097656250000000000000000000000000000),((44450952547681403761389211:ℚ)/1108992000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((283143313:ℚ)/400000000),((1790489751:ℚ)/2500000000),((-1630489751:ℚ)/5625000000),((-244743313:ℚ)/1134500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1862883503:ℚ)/5000000000),((1114166282179901582133362499920877548076624548257:ℚ)/102670585918945312500000000000000000000000000000000),((2770650562193852741834251:ℚ)/69312000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-5:ℚ)/16),((-1:ℚ)/4),((892247521:ℚ)/1250000000),((7191661797:ℚ)/10000000000),((-6551661797:ℚ)/22690000000),((-772247521:ℚ)/3560156250),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3504802823:ℚ)/10000000000),((576177577466427698547337542880712927157433720736365181:ℚ)/53326176279886811971664428710937500000000000000000000000),((44192076465304543533349459:ℚ)/1108992000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7167678699:ℚ)/10000000000),((7221364463:ℚ)/10000000000),((-6581364463:ℚ)/22785000000),((-6207678699:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((16945799:ℚ)/50000000),((3598132703756991523912483704365522762499795355635024807743:ℚ)/333140282475000000000000000000000000000000000000000000000000),((14710663915432697710122873:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-5:ℚ)/16),((-1:ℚ)/4),((7197377139:ℚ)/10000000000),((7251067003:ℚ)/10000000000),((-6611067003:ℚ)/22880000000),((-6237377139:ℚ)/28718750000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((326959233:ℚ)/1000000000),((114279929427766230152525116321239481099323729572253692373:ℚ)/10584800046634674072265625000000000000000000000000000000000),((14690660580456610756760753:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((225846109:ℚ)/312500000),((7280769419:ℚ)/10000000000),((-6640769419:ℚ)/22975000000),((-195846109:ℚ)/901171875),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3145652389:ℚ)/10000000000),((21266078118216526572516746825177920594524749011961:ℚ)/1970424038436671253293752670288085937500000000000000),((14670682150267162940849937:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((1814193437:ℚ)/2500000000),((3670086943:ℚ)/5000000000),((-3350086943:ℚ)/11535000000),((-1574193437:ℚ)/7268750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3016800547:ℚ)/10000000000),((29973530998796411465824096637026713643293446801277824759:ℚ)/2768705812323760986328125000000000000000000000000000000000),((3664214303851252116951833:ℚ)/92416000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((1829042501:ℚ)/2500000000),((59196623:ℚ)/80000000),((-54076623:ℚ)/186080000),((-1589042501:ℚ)/7328125000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((137078171:ℚ)/500000000),((46416103192347555911195175200313924566497042449978698581:ℚ)/4290714296114444732666015625000000000000000000000000000000),((935492769131650531513:ℚ)/23658496000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1475113183:ℚ)/2000000000),((3729490699:ℚ)/5000000000),((-3409490699:ℚ)/11725000000),((-1283113183:ℚ)/5910000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2436279991:ℚ)/10000000000),((272542002956353852911025113453418153395520428812117081:ℚ)/25211812057031250000000000000000000000000000000000000000),((3644347855649279713633617:ℚ)/92416000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((743496149:ℚ)/1000000000),((7577787089:ℚ)/10000000000),((-6937787089:ℚ)/23640000000),((-647496149:ℚ)/3002500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((208780489:ℚ)/1000000000),((135890890259928670077144843113455135614338255096405099:ℚ)/12497598244519042968750000000000000000000000000000000000),((14550437481137061777752057:ℚ)/369664000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7553751663:ℚ)/10000000000),((1924147761:ℚ)/2500000000),((-1764147761:ℚ)/6005000000),((-6593751663:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((551882659:ℚ)/5000000000),((1156193652083604610526959530616166531915965347119175559327:ℚ)/106486008203125000000000000000000000000000000000000000000000),((2001517870734973:ℚ)/51200000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((959067573:ℚ)/1250000000),((4085895517:ℚ)/5000000000),((-3765895517:ℚ)/12200000000),((-279689191:ℚ)/1350000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1755839950107041514916887873882608722663994163464137:ℚ)/156336328125000000000000000000000000000000000000000000),((311859:ℚ)/8000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((2036921213:ℚ)/2500000000),((2014480183:ℚ)/2000000000),((-1886480183:ℚ)/5184000000),((-1796921213:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3141545624018397450618911049323700418816765195997028077:ℚ)/253125000000000000000000000000000000000000000000000000000),((311859:ℚ)/8000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((5024062411:ℚ)/5000000000),((6936558361:ℚ)/5000000000),((-6616558361:ℚ)/16000000000),((-4544062411:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((687071867310621877990188044754862646746021470777644713:ℚ)/49276350000000000000000000000000000000000000000000000000),((311859:ℚ)/8000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC12
#check @N11Formalization.C450SeventhGroupedC12.bound
#print axioms N11Formalization.C450SeventhGroupedC12.valid0
#print axioms N11Formalization.C450SeventhGroupedC12.valid1
#print axioms N11Formalization.C450SeventhGroupedC12.valid2
#print axioms N11Formalization.C450SeventhGroupedC12.valid3
#print axioms N11Formalization.C450SeventhGroupedC12.valid4
#print axioms N11Formalization.C450SeventhGroupedC12.valid5
#print axioms N11Formalization.C450SeventhGroupedC12.valid6
#print axioms N11Formalization.C450SeventhGroupedC12.valid7
#print axioms N11Formalization.C450SeventhGroupedC12.valid8
#print axioms N11Formalization.C450SeventhGroupedC12.valid9
#print axioms N11Formalization.C450SeventhGroupedC12.valid10
#print axioms N11Formalization.C450SeventhGroupedC12.valid11
#print axioms N11Formalization.C450SeventhGroupedC12.valid12
#print axioms N11Formalization.C450SeventhGroupedC12.valid13
#print axioms N11Formalization.C450SeventhGroupedC12.valid14
#print axioms N11Formalization.C450SeventhGroupedC12.valid15
#print axioms N11Formalization.C450SeventhGroupedC12.valid16
#print axioms N11Formalization.C450SeventhGroupedC12.valid17
#print axioms N11Formalization.C450SeventhGroupedC12.valid18
#print axioms N11Formalization.C450SeventhGroupedC12.bound
#print axioms N11Formalization.C450SeventhGroupedC12.endpoint_checks
