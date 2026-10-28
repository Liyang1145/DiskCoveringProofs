import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((3336596287:ℚ)/5000000000),((3450669347:ℚ)/5000000000),((-2090669347:ℚ)/6200000000),((-4052058003:ℚ)/16850000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4990206751:ℚ)/10000000000),((664437090611348270742540449822208569:ℚ)/2979100000000000000000000000000000000),((193874199728954079100620539:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6794276291:ℚ)/10000000000),((6961827093:ℚ)/10000000000),((-4241827093:ℚ)/12637500000),((-25159934037:ℚ)/102050000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4646382537:ℚ)/10000000000),((86762081596747438787959902133896382334568951555456637:ℚ)/394197208786010742187500000000000000000000000000000000),((2074342455200378530994651:ℚ)/10240000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((342739231:ℚ)/500000000),((438893399:ℚ)/625000000),((-268893399:ℚ)/797265625),((-1279174617:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4465431159:ℚ)/10000000000),((4299135472018901742787764271467342907977091257363:ℚ)/19491073995828628540039062500000000000000000000000),((1838484190854503693596091:ℚ)/9241600000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6915271451:ℚ)/10000000000),((3541370583:ℚ)/5000000000),((-2181370583:ℚ)/6437500000),((-412807939:ℚ)/1650000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4277434169:ℚ)/10000000000),((719828540499971829390676641798913809659492950989543:ℚ)/3256580233573913574218750000000000000000000000000000),((721873412110491134077387331:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6975737397:ℚ)/10000000000),((7143168017:ℚ)/10000000000),((-491463113:ℚ)/1443750000),((-26430161779:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((408141173:ℚ)/1000000000),((9017723116573491534981990288855727756230374000047:ℚ)/40711212158203125000000000000000000000000000000000),((708276781828461214453122979:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3518091523:ℚ)/5000000000),((7203575491:ℚ)/10000000000),((-4483575491:ℚ)/13112500000),((-462987609:ℚ)/1825000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1938069963:ℚ)/5000000000),((1563865024603185226213265757310793668664211539174578579:ℚ)/7045414117431640625000000000000000000000000000000000000),((173650934011879823110972499:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((7096608963:ℚ)/10000000000),((58111713:ℚ)/80000000),((-36351713:ℚ)/105850000),((-27276262741:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3660056099:ℚ)/10000000000),((618274546170278661823376222398235036181117581491:ℚ)/2779610042871093750000000000000000000000000000000),((680854227389975786207939539:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((3578507847:ℚ)/5000000000),((7324334433:ℚ)/10000000000),((-4604334433:ℚ)/13350000000),((-13849554929:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((686222211:ℚ)/2000000000),((4971789461756186260324091682371831553604756800849227171:ℚ)/22305659765625000000000000000000000000000000000000000000),((166757052446746609868576779:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1804350941:ℚ)/2500000000),((7384686911:ℚ)/10000000000),((-4664686911:ℚ)/13468750000),((-7030456587:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1593263213:ℚ)/5000000000),((1705397454256300289927437715363033579313761922692090119:ℚ)/7635401821136474609375000000000000000000000000000000000),((113075768537031944119451:ℚ)/640000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3638886839:ℚ)/5000000000),((7505340277:ℚ)/10000000000),((-4785340277:ℚ)/13587500000),((-2038886839:ℚ)/7900000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2922370127:ℚ)/10000000000),((333927902408855826640734002130234400324104502537295311:ℚ)/1469839671707153320312500000000000000000000000000000000),((159786618220192856043897451:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((7398460973:ℚ)/10000000000),((7746453011:ℚ)/10000000000),((-5026453011:ℚ)/13825000000),((-29389226811:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((577021797:ℚ)/2500000000),((276664084666716345475159586332665317916022843622331397:ℚ)/1179634326171875000000000000000000000000000000000000000),((610958190999867605759315699:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((7639638029:ℚ)/10000000000),((8708745223:ℚ)/10000000000),((-5988745223:ℚ)/14300000000),((-10359155401:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1861639943149545705799298278175804009194539918925146901:ℚ)/6853610156250000000000000000000000000000000000000000000),((39000433:ℚ)/256000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((4301074183:ℚ)/5000000000),((5313113943:ℚ)/5000000000),((-3953113943:ℚ)/8100000000),((-18907519281:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((96438899905143690546105665766039502848834195386612989:ℚ)/311391210937500000000000000000000000000000000000000000),((39000433:ℚ)/256000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((1314992443:ℚ)/1250000000),((2889327191:ℚ)/2000000000),((-2345327191:ℚ)/4000000000),((-2134982367:ℚ)/9200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((7795385716325403184587426529713987:ℚ)/20000000000000000000000000000000000),((39000433:ℚ)/256000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC09
#check @N11Formalization.C450Source36GroupedC09.bound
#print axioms N11Formalization.C450Source36GroupedC09.valid0
#print axioms N11Formalization.C450Source36GroupedC09.valid1
#print axioms N11Formalization.C450Source36GroupedC09.valid2
#print axioms N11Formalization.C450Source36GroupedC09.valid3
#print axioms N11Formalization.C450Source36GroupedC09.valid4
#print axioms N11Formalization.C450Source36GroupedC09.valid5
#print axioms N11Formalization.C450Source36GroupedC09.valid6
#print axioms N11Formalization.C450Source36GroupedC09.valid7
#print axioms N11Formalization.C450Source36GroupedC09.valid8
#print axioms N11Formalization.C450Source36GroupedC09.valid9
#print axioms N11Formalization.C450Source36GroupedC09.valid10
#print axioms N11Formalization.C450Source36GroupedC09.valid11
#print axioms N11Formalization.C450Source36GroupedC09.valid12
#print axioms N11Formalization.C450Source36GroupedC09.valid13
#print axioms N11Formalization.C450Source36GroupedC09.bound
#print axioms N11Formalization.C450Source36GroupedC09.endpoint_checks
