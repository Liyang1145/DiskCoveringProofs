import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((6284424839:ℚ)/10000000000),((6567605347:ℚ)/10000000000),((-4167605347:ℚ)/24800000000),((-8613274517:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1493068337:ℚ)/2500000000),((20359449626469649476221416082723493752496595240859216177897:ℚ)/317573784375000000000000000000000000000000000000000000000000),((-58884354702452379030480321:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((3261482537:ℚ)/5000000000),((3403086857:ℚ)/5000000000),((-2203086857:ℚ)/12875000000),((-4664447611:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1077756483:ℚ)/2000000000),((778417938836057407327247171408007017493079891562299936789:ℚ)/12253242431250000000000000000000000000000000000000000000000),((-32801895207119052483207969:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6761430833:ℚ)/10000000000),((1385085941:ℚ)/2000000000),((-905085941:ℚ)/5340000000),((-10044292499:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4741920201:ℚ)/10000000000),((22305587719387048657473967785684818144132717401131095868603:ℚ)/357214155521875000000000000000000000000000000000000000000000),((-203646591632602808521653489:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((6880638243:ℚ)/10000000000),((1761167051:ℚ)/2500000000),((-1161167051:ℚ)/6793750000),((-10401914729:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((274124933:ℚ)/625000000),((13406775521770561592040724118865830470646391132016602540773:ℚ)/215420102108203125000000000000000000000000000000000000000000),((-239910224180864767176530649:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((139996597:ℚ)/200000000),((888035147:ℚ)/1250000000),((-84005021:ℚ)/493750000),((-215189791:ℚ)/2231000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4000789583:ℚ)/10000000000),((109089173654358002641352951016460607643985676798729:ℚ)/1766379870507812500000000000000000000000000000000000),((-110481445436015501088009:ℚ)/5914624000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((3529709991:ℚ)/5000000000),((1432778021:ℚ)/2000000000),((-952778021:ℚ)/5577500000),((-5469129973:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3794431189:ℚ)/10000000000),((896785316413317621243856033310905008455059223126457811553:ℚ)/14541140198707580566406250000000000000000000000000000000000),((-73590385106894298271748481:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((355950323:ℚ)/500000000),((7223495093:ℚ)/10000000000),((-4823495093:ℚ)/28125000000),((-555850969:ℚ)/5672500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1788402917:ℚ)/5000000000),((87825769441044341651801991621744307701172721443513:ℚ)/1425980359985351562500000000000000000000000000000000),((-781317479718559229599929:ℚ)/36966400000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((7178589379:ℚ)/10000000000),((7283096239:ℚ)/10000000000),((-4883096239:ℚ)/28362500000),((-11295768137:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((669142187:ℚ)/2000000000),((653002080030975294621369457709819207403594521581831685115861:ℚ)/10616041092800000000000000000000000000000000000000000000000000),((-330699995362728853393318041:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((3619084413:ℚ)/5000000000),((183567341:ℚ)/250000000),((-123567341:ℚ)/715000000),((-5737253239:ℚ)/57675000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((774532207:ℚ)/2500000000),((47479569624954107146285460842869939228087730239541919:ℚ)/772835042226791381835937500000000000000000000000000000),((-241607046994495641543729:ℚ)/10240000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((912218111:ℚ)/1250000000),((7402287387:ℚ)/10000000000),((-1667429129:ℚ)/9612500000),((-1456654333:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1414864937:ℚ)/5000000000),((453061594231717045440800723823630728296607431349827884101:ℚ)/7383215499530029296875000000000000000000000000000000000000),((-5735449350570025118072721:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((147146353:ℚ)/200000000),((1880366069:ℚ)/2500000000),((-1280366069:ℚ)/7268750000),((-236639059:ℚ)/2364000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2533901783:ℚ)/10000000000),((27370013698523465816056167971295334960401306261910163:ℚ)/444578439950000000000000000000000000000000000000000000),((-154105827035443701988209:ℚ)/5914624000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((7476453589:ℚ)/10000000000),((193994449:ℚ)/250000000),((-133994449:ℚ)/738750000),((-12189360767:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((45139149:ℚ)/250000000),((207758773362605132418480415056109371248328290596281980470969:ℚ)/3353644275000000000000000000000000000000000000000000000000000),((-421679156208079521663285321:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((3857344619:ℚ)/5000000000),((4118130757:ℚ)/5000000000),((-2918130757:ℚ)/15250000000),((-6452033857:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1083580020976254651383985830547209073590098843477005668983:ℚ)/17289547200000000000000000000000000000000000000000000000000),((-31819827:ℚ)/1024000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((2047757643:ℚ)/2500000000),((2028156307:ℚ)/2000000000),((-1548156307:ℚ)/6480000000),((-3583272929:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((40333153881177988930005555451042989481052467391874475651:ℚ)/600000000000000000000000000000000000000000000000000000000),((-31819827:ℚ)/1024000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10095117703:ℚ)/10000000000),((6973039969:ℚ)/5000000000),((-5773039969:ℚ)/20000000000),((-20045353109:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1895852247595857096021455290575593130666918155290865146991:ℚ)/25229491200000000000000000000000000000000000000000000000000),((-31819827:ℚ)/1024000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source17 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC13
#check @N11Formalization.C450Source17GroupedC13.bound
#print axioms N11Formalization.C450Source17GroupedC13.valid0
#print axioms N11Formalization.C450Source17GroupedC13.valid1
#print axioms N11Formalization.C450Source17GroupedC13.valid2
#print axioms N11Formalization.C450Source17GroupedC13.valid3
#print axioms N11Formalization.C450Source17GroupedC13.valid4
#print axioms N11Formalization.C450Source17GroupedC13.valid5
#print axioms N11Formalization.C450Source17GroupedC13.valid6
#print axioms N11Formalization.C450Source17GroupedC13.valid7
#print axioms N11Formalization.C450Source17GroupedC13.valid8
#print axioms N11Formalization.C450Source17GroupedC13.valid9
#print axioms N11Formalization.C450Source17GroupedC13.valid10
#print axioms N11Formalization.C450Source17GroupedC13.valid11
#print axioms N11Formalization.C450Source17GroupedC13.valid12
#print axioms N11Formalization.C450Source17GroupedC13.valid13
#print axioms N11Formalization.C450Source17GroupedC13.valid14
#print axioms N11Formalization.C450Source17GroupedC13.bound
#print axioms N11Formalization.C450Source17GroupedC13.endpoint_checks
