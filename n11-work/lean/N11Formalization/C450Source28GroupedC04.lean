import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((867715067:ℚ)/1250000000),((3552565251:ℚ)/5000000000),((-37863348263:ℚ)/49600000000),((-2063145201:ℚ)/3129687500),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((2096375561:ℚ)/5000000000),((1610691914226719885673146171017039354810834533771445029643573:ℚ)/4895611294474240000000000000000000000000000000000000000000000),((156422663342767955971494021:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((700146087:ℚ)/1000000000),((7164805293:ℚ)/10000000000),((-76502468809:ℚ)/100150000000),((-556146087:ℚ)/842500000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((15606547:ℚ)/39062500),((704074892765993870875812290508684559057129969621628553946324993:ℚ)/2139015515138350781250000000000000000000000000000000000000000000),((100194012695576360592374141:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1765298569:ℚ)/2500000000),((361223723:ℚ)/500000000),((-3863908399:ℚ)/5055000000),((-4215895707:ℚ)/6378125000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((1894061673:ℚ)/5000000000),((692159292213237762223489182284518265400798504897711355901:ℚ)/2101887773302935058593750000000000000000000000000000000000),((32985832945979813025840591:ℚ)/48640000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7120920949:ℚ)/10000000000),((906788373:ℚ)/1250000000),((-746788373:ℚ)/981250000),((-5680920949:ℚ)/8543750000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((892400919:ℚ)/2500000000),((2697610623121116555155684051707684279152986185162150967981:ℚ)/8275939728100204467773437500000000000000000000000000000000),((10028354226773968703954533989:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((357539091:ℚ)/500000000),((7284138161:ℚ)/10000000000),((-26017932031:ℚ)/34175000000),((-856617273:ℚ)/1287500000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3455410173:ℚ)/10000000000),((2588693251225457321712586257323159123086290067430829768135823:ℚ)/7939648777900488281250000000000000000000000000000000000000000),((25081122676089527838639509:ℚ)/36966400000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7180641079:ℚ)/10000000000),((731396801:ℚ)/1000000000),((-7844158413:ℚ)/10300000000),((-17221923237:ℚ)/25868750000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((3337479811:ℚ)/10000000000),((381572478737975069386094241641953920698048435611508784679863:ℚ)/1169991062647937500000000000000000000000000000000000000000000),((10036529214872096982318857949:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3605249373:ℚ)/5000000000),((1835949137:ℚ)/2500000000),((-19707338781:ℚ)/25868750000),((-961749791:ℚ)/1443750000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((3215400799:ℚ)/10000000000),((14268028096255037804772835972922116394253680209025711459983:ℚ)/43737743885010910034179687500000000000000000000000000000000),((132113087689487612585126999:ℚ)/194560000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3620177423:ℚ)/5000000000),((3686811897:ℚ)/5000000000),((-39608554661:ℚ)/51975000000),((-8700532269:ℚ)/13053125000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((617736111:ℚ)/2000000000),((113542476453248243901311107615058779812083690153266421482145981:ℚ)/347968383317153833007812500000000000000000000000000000000000000),((2511161355804679271383787181:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3635104699:ℚ)/5000000000),((3701724883:ℚ)/5000000000),((-39802423479:ℚ)/52212500000),((-8745314097:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2956721697:ℚ)/10000000000),((79877046391814925378080188036312071597576233947567916491750869:ℚ)/244734089450337014770507812500000000000000000000000000000000000),((2512170373982566581013513989:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((292002497:ℚ)/400000000),((1492619591:ℚ)/2000000000),((-16076054683:ℚ)/20980000000),((-703207491:ℚ)/1058500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((704696963:ℚ)/2500000000),((1168708060416192353873586160478996212598459122443877964814049:ℚ)/3543360380202850000000000000000000000000000000000000000000000),((16096436854457219709380301:ℚ)/23658496000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((3679881993:ℚ)/5000000000),((7522741251:ℚ)/10000000000),((-81155636263:ℚ)/105850000000),((-2959881993:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((630257409:ℚ)/2500000000),((66343320123744389091820390742521922426021494540841296217621:ℚ)/201071152050976562500000000000000000000000000000000000000000),((2517067791844692979409216861:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7419459689:ℚ)/10000000000),((7642013681:ℚ)/10000000000),((-27568725951:ℚ)/35600000000),((-17938379067:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((436806199:ℚ)/2000000000),((112158637890534147451185357622260478487166975230088967669821021:ℚ)/333187806544400000000000000000000000000000000000000000000000000),((10080683208271204003886928669:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7538834147:ℚ)/10000000000),((485079253:ℚ)/625000000),((-5266030289:ℚ)/6793750000),((-2613786063:ℚ)/3950000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1269563487:ℚ)/10000000000),((193039504908416253174877503205153594639674026520022673777:ℚ)/573329336945271492004394531250000000000000000000000000000),((10066113452142812872535731701:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((3829093493:ℚ)/5000000000),((7999726217:ℚ)/10000000000),((-87356440821:ℚ)/110600000000),((-847934589:ℚ)/1300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((38390774576616665645390989806681886576561836932544030788787:ℚ)/109923045050000000000000000000000000000000000000000000000000),((696576039:ℚ)/1024000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((3948416079:ℚ)/5000000000),((4476497091:ℚ)/5000000000),((-3836497091:ℚ)/4400000000),((-1076138693:ℚ)/1800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((502602247829684493105585295645127191908812247501551209:ℚ)/1197900000000000000000000000000000000000000000000000000),((696576039:ℚ)/1024000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((4425368631:ℚ)/5000000000),((2171532127:ℚ)/2000000000),((-2766879739:ℚ)/2880000000),((-11116105893:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13801593011784861131527635770100373187138981667890803:ℚ)/27993600000000000000000000000000000000000000000000000),((696576039:ℚ)/1024000000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10756311941:ℚ)/10000000000),((14663130429:ℚ)/10000000000),(-1:ℚ),((-9316311941:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5795661826539256221343737:ℚ)/10580000000000000000000000),((696576039:ℚ)/1024000000)⟩
theorem valid16 : Valid source28 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4101:ℚ)/6400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((4101:ℚ)/6400) ((4139:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source28 nn0 nn1 Qcell ((4139:ℚ)/6400) ((4177:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source28 nn0 nn1 Qcell ((4101:ℚ)/6400) ((4177:ℚ)/6400) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((4177:ℚ)/6400) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source28 nn0 nn1 Qcell ((4177:ℚ)/6400) ((2117:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((1087:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source28 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source28 nn0 nn1 Qcell ((4177:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC04
#check @N11Formalization.C450Source28GroupedC04.bound
#print axioms N11Formalization.C450Source28GroupedC04.valid0
#print axioms N11Formalization.C450Source28GroupedC04.valid1
#print axioms N11Formalization.C450Source28GroupedC04.valid2
#print axioms N11Formalization.C450Source28GroupedC04.valid3
#print axioms N11Formalization.C450Source28GroupedC04.valid4
#print axioms N11Formalization.C450Source28GroupedC04.valid5
#print axioms N11Formalization.C450Source28GroupedC04.valid6
#print axioms N11Formalization.C450Source28GroupedC04.valid7
#print axioms N11Formalization.C450Source28GroupedC04.valid8
#print axioms N11Formalization.C450Source28GroupedC04.valid9
#print axioms N11Formalization.C450Source28GroupedC04.valid10
#print axioms N11Formalization.C450Source28GroupedC04.valid11
#print axioms N11Formalization.C450Source28GroupedC04.valid12
#print axioms N11Formalization.C450Source28GroupedC04.valid13
#print axioms N11Formalization.C450Source28GroupedC04.valid14
#print axioms N11Formalization.C450Source28GroupedC04.valid15
#print axioms N11Formalization.C450Source28GroupedC04.valid16
#print axioms N11Formalization.C450Source28GroupedC04.bound
#print axioms N11Formalization.C450Source28GroupedC04.endpoint_checks
