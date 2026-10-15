import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((2797999353:ℚ)/5000000000),((6143676783:ℚ)/10000000000),((7328665157:ℚ)/8900000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7431873509:ℚ)/10000000000),((-385703705242468823395668477358862047:ℚ)/4406056250000000000000000000000000000),((-440482967214836148354458161:ℚ)/1386240000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6071283607:ℚ)/10000000000),((797674279:ℚ)/1250000000),((47298985249:ℚ)/55300000000),((2649022837:ℚ)/2670000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3227050851:ℚ)/5000000000),((-157817005234288408658198749028157533244536021036163346219:ℚ)/1585428534375000000000000000000000000000000000000000000000),((-579994924000017472815620507:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((6308911363:ℚ)/10000000000),((51711697:ℚ)/78125000),((48962379541:ℚ)/57200000000),((171135091:ℚ)/172812500),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((739342017:ℚ)/1250000000),((-58255274364340744607099621331855111529247652649904328973:ℚ)/584841400000000000000000000000000000000000000000000000000),((-572639297490933736867091267:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((102289541:ℚ)/156250000),((421121483:ℚ)/625000000),((791026787:ℚ)/908593750),((1391364449:ℚ)/1430000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((66600637:ℚ)/125000000),((-123141074210368738329449958444167008156349482744813:ℚ)/1172004451602697372436523437500000000000000000000000),((-69456323597625611620729:ℚ)/225625000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6665337331:ℚ)/10000000000),((3428393567:ℚ)/5000000000),((51457361317:ℚ)/59100000000),((11309180701:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2505880843:ℚ)/5000000000),((-5644075951049161248806232544976083411806774096823953623:ℚ)/53756528906250000000000000000000000000000000000000000000),((-565310172534777783369829923:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1696035553:ℚ)/2500000000),((348781379:ℚ)/500000000),((13072248871:ℚ)/15012500000),((1148744137:ℚ)/1182000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4676052259:ℚ)/10000000000),((-832053875145985514749739689208181926108206935983212549:ℚ)/7929948124694824218750000000000000000000000000000000000),((-35102166986044058506858987:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6902945357:ℚ)/10000000000),((3517523369:ℚ)/5000000000),((53120617499:ℚ)/60525000000),((11576570107:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((4316365957:ℚ)/10000000000),((-55864342723183401633811684873762843370310320364055599041:ℚ)/519655680944824218750000000000000000000000000000000000000),((-559809783179449735493081507:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((6962346303:ℚ)/10000000000),((7094465207:ℚ)/10000000000),((53536424121:ℚ)/61000000000),((23331395621:ℚ)/24210000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2062789789:ℚ)/5000000000),((-76214520309214031216831817263098677058165518173689082673:ℚ)/709315625000000000000000000000000000000000000000000000000),((-1673917410555821556738384961:ℚ)/5544960000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1404349369:ℚ)/2000000000),((7153883003:ℚ)/10000000000),((10790445583:ℚ)/12295000000),((23509649009:ℚ)/24400000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((61345133:ℚ)/156250000),((-38985451552096821865910067404301960799178773173127719:ℚ)/363007533666992187500000000000000000000000000000000000),((-22245411500354843571577723:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7081146991:ℚ)/10000000000),((7213300143:ℚ)/10000000000),((54368028937:ℚ)/61950000000),((23687900429:ℚ)/24590000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((3716487447:ℚ)/10000000000),((-79755191140561706807954310578555457662638460361737052361:ℚ)/742974577734375000000000000000000000000000000000000000000),((-554298234620443897755678283:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((111571043:ℚ)/156250000),((7332132511:ℚ)/10000000000),((855997301:ℚ)/982812500),((24044397533:ℚ)/24780000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1747476917:ℚ)/5000000000),((-233098469003141393359953889419162048784600841550971:ℚ)/2224965593218803405761718750000000000000000000000000),((-2150825410449863811571187:ℚ)/7220000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((28356817:ℚ)/39062500),((298038497:ℚ)/400000000),((434495438:ℚ)/498828125),((976035491:ℚ)/1006400000),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((300539241:ℚ)/1000000000),((-5077644624117353143352534282861606309393397779307:ℚ)/48485606280155479907989501953125000000000000000000),((-2136476101768173622533237:ℚ)/7220000000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((737814211:ℚ)/1000000000),((3784894997:ℚ)/5000000000),((5644699477:ℚ)/6480000000),((12378684991:ℚ)/12770000000),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((605546973:ℚ)/2500000000),((-29673058993870888486455550226090356992971207004899143:ℚ)/283435200000000000000000000000000000000000000000000000),((-5432649694930653425083203:ℚ)/18483200000000000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((749693769:ℚ)/1000000000),((8520337199:ℚ)/10000000000),((5727856383:ℚ)/7240000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((16487323:ℚ)/100000000),((-5675417864694087643966060382182780487872592448921631:ℚ)/74121762500000000000000000000000000000000000000000000),((-16270552222730071324621969:ℚ)/55449600000000000000000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((8447259251:ℚ)/10000000000),((4735390181:ℚ)/5000000000),((63930814757:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-31718891547649203823701097152868923084950876519484929749:ℚ)/400000000000000000000000000000000000000000000000000000000),((-2347541:ℚ)/8000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((939751969:ℚ)/1000000000),((13271942599:ℚ)/10000000000),((7058263783:ℚ)/11040000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-4855924230250152045334666765081373:ℚ)/168196608000000000000000000000000000),((-2347541:ℚ)/8000000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((61:ℚ)/80) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((1277:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((1277:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source17 nn0 nn1 Qcell ((1277:ℚ)/1600) ((181:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source17 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source17 nn0 nn1 Qcell ((1277:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC31
#check @N11Formalization.C450Source17GroupedC31.bound
#print axioms N11Formalization.C450Source17GroupedC31.valid0
#print axioms N11Formalization.C450Source17GroupedC31.valid1
#print axioms N11Formalization.C450Source17GroupedC31.valid2
#print axioms N11Formalization.C450Source17GroupedC31.valid3
#print axioms N11Formalization.C450Source17GroupedC31.valid4
#print axioms N11Formalization.C450Source17GroupedC31.valid5
#print axioms N11Formalization.C450Source17GroupedC31.valid6
#print axioms N11Formalization.C450Source17GroupedC31.valid7
#print axioms N11Formalization.C450Source17GroupedC31.valid8
#print axioms N11Formalization.C450Source17GroupedC31.valid9
#print axioms N11Formalization.C450Source17GroupedC31.valid10
#print axioms N11Formalization.C450Source17GroupedC31.valid11
#print axioms N11Formalization.C450Source17GroupedC31.valid12
#print axioms N11Formalization.C450Source17GroupedC31.valid13
#print axioms N11Formalization.C450Source17GroupedC31.valid14
#print axioms N11Formalization.C450Source17GroupedC31.valid15
#print axioms N11Formalization.C450Source17GroupedC31.bound
#print axioms N11Formalization.C450Source17GroupedC31.endpoint_checks
