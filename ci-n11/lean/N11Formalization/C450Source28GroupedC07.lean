import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3362541733:ℚ)/5000000000),((3468627057:ℚ)/5000000000),((-2636627057:ℚ)/4960000000),((-7207625199:ℚ)/16850000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((969122541:ℚ)/2000000000),((253412008794293331332566061597155694962124467160418498739:ℚ)/926918236718750000000000000000000000000000000000000000000),((28666230319950358599589017:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((684497017:ℚ)/1000000000),((3498579861:ℚ)/5000000000),((-2666579861:ℚ)/5055000000),((-4432473153:ℚ)/10205000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((449524171:ℚ)/1000000000),((1131969847356250386400362809070977847954576859724421113:ℚ)/4197108703677246093750000000000000000000000000000000000),((1131242670756718632604017:ℚ)/3696640000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6904897427:ℚ)/10000000000),((1764263853:ℚ)/2500000000),((-1348263853:ℚ)/2551250000),((-44864076843:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4310222347:ℚ)/10000000000),((3762242531046903613010939367234180066724985372181280435450793:ℚ)/13939098793750000000000000000000000000000000000000000000000000),((112347383437294395614164137:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1741203589:ℚ)/2500000000),((3558470731:ℚ)/5000000000),((-2726470731:ℚ)/5150000000),((-1261203589:ℚ)/2887500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((411747279:ℚ)/1000000000),((3139615528526479660245085210974285774560608379928429619:ℚ)/11623702450561523437500000000000000000000000000000000000),((6972882921673257329377113:ℚ)/23104000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7024721247:ℚ)/10000000000),((1429376191:ℚ)/2000000000),((-40613933:ℚ)/77000000),((-45942491223:ℚ)/104425000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((195792333:ℚ)/500000000),((3342242797675651771777217053503033118231008453741542642971:ℚ)/12454649722436523437500000000000000000000000000000000000000),((110780495520492424886306177:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3527335507:ℚ)/5000000000),((3588409069:ℚ)/5000000000),((-2756409069:ℚ)/5221250000),((-23106019563:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3811265499:ℚ)/10000000000),((252813851460433729469222612944814811178890356709349480675449:ℚ)/941718232592382812500000000000000000000000000000000000000000),((27596509758288355153536297:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((885577297:ℚ)/1250000000),((7206753041:ℚ)/10000000000),((-5542753041:ℚ)/10490000000),((-1936731891:ℚ)/4390625000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((1851944701:ℚ)/5000000000),((1490341469994689926637451961752765533948865804812408121:ℚ)/5549253227472305297851562500000000000000000000000000000),((1718601380818763625399777:ℚ)/5776000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1778640841:ℚ)/2500000000),((56536607:ℚ)/78125000),((-174146428:ℚ)/329296875),((-11687767569:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3593467181:ℚ)/10000000000),((26231358075839199958470464587939246890310014903189072199993:ℚ)/97633802755847167968750000000000000000000000000000000000000),((6849615212391521582642193:ℚ)/23104000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7144506011:ℚ)/10000000000),((3633308067:ℚ)/5000000000),((-2801308067:ℚ)/5292500000),((-47020554099:ℚ)/106325000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((434963523:ℚ)/1250000000),((4274594679675289801938828870601025064643043513824769602371877:ℚ)/15904024992227441406250000000000000000000000000000000000000000),((109196103939486525809650713:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((7174446349:ℚ)/10000000000),((57004253:ℚ)/78125000),((-176017012:ℚ)/332265625),((-15763339047:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((420284131:ℚ)/1250000000),((80615514162002266677702697274142873508224219158179028270521:ℚ)/299823315700000000000000000000000000000000000000000000000000),((108797269833167558483691753:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((720438441:ℚ)/1000000000),((7356394441:ℚ)/10000000000),((-5692394441:ℚ)/10680000000),((-4755945969:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((405095181:ℚ)/1250000000),((2208726563247637078001448739033162542062755215813513577:ℚ)/8154609144973754882812500000000000000000000000000000000),((1083973409115765812131793:ℚ)/3696640000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7264253821:ℚ)/10000000000),((115878689:ℚ)/156250000),((-89878689:ℚ)/168359375),((-48098284389:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((11654287:ℚ)/39062500),((937710827610434810528320770869676824529789317686814645749401:ℚ)/3459759573706250000000000000000000000000000000000000000000000),((107594198035125536738566473:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((1831028621:ℚ)/2500000000),((7535895079:ℚ)/10000000000),((-5871895079:ℚ)/10870000000),((-12159257589:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((67567097:ℚ)/250000000),((616763626784767710073894022062922536961722227771703133713:ℚ)/2243959396960449218750000000000000000000000000000000000000),((6674167130621660219511273:ℚ)/23104000000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7443810481:ℚ)/10000000000),((194378037:ℚ)/250000000),((-152778037:ℚ)/276500000),((-49714294329:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1015431761:ℚ)/5000000000),((1460084636052606033939714363779403933098209912598577494623403:ℚ)/5174676707200000000000000000000000000000000000000000000000000),((291297724005638643295353:ℚ)/1024000000000000000000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((384155357:ℚ)/500000000),((4365502763:ℚ)/5000000000),((-3533502763:ℚ)/5720000000),((-288155357:ℚ)/720000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((260918072066665294522586270383958864027786112889317109:ℚ)/809780400000000000000000000000000000000000000000000000),((35667183:ℚ)/128000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((2159807563:ℚ)/2500000000),((10639397877:ℚ)/10000000000),((-8975397877:ℚ)/12960000000),((-15118268067:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((14854735047388464365138846177241034941890007014333531101:ℚ)/40814668800000000000000000000000000000000000000000000000),((35667183:ℚ)/128000000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10547962659:ℚ)/10000000000),((14449223211:ℚ)/10000000000),((-12785223211:ℚ)/16000000000),((-25883887977:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4430667221451195424294092711418981731492803392405477753243:ℚ)/10156800000000000000000000000000000000000000000000000000000),((35667183:ℚ)/128000000)⟩
theorem valid16 : Valid source28 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((1087:ℚ)/1600) :=
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
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC07
#check @N11Formalization.C450Source28GroupedC07.bound
#print axioms N11Formalization.C450Source28GroupedC07.valid0
#print axioms N11Formalization.C450Source28GroupedC07.valid1
#print axioms N11Formalization.C450Source28GroupedC07.valid2
#print axioms N11Formalization.C450Source28GroupedC07.valid3
#print axioms N11Formalization.C450Source28GroupedC07.valid4
#print axioms N11Formalization.C450Source28GroupedC07.valid5
#print axioms N11Formalization.C450Source28GroupedC07.valid6
#print axioms N11Formalization.C450Source28GroupedC07.valid7
#print axioms N11Formalization.C450Source28GroupedC07.valid8
#print axioms N11Formalization.C450Source28GroupedC07.valid9
#print axioms N11Formalization.C450Source28GroupedC07.valid10
#print axioms N11Formalization.C450Source28GroupedC07.valid11
#print axioms N11Formalization.C450Source28GroupedC07.valid12
#print axioms N11Formalization.C450Source28GroupedC07.valid13
#print axioms N11Formalization.C450Source28GroupedC07.valid14
#print axioms N11Formalization.C450Source28GroupedC07.valid15
#print axioms N11Formalization.C450Source28GroupedC07.valid16
#print axioms N11Formalization.C450Source28GroupedC07.bound
#print axioms N11Formalization.C450Source28GroupedC07.endpoint_checks
