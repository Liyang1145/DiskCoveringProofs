import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1316812791:ℚ)/2000000000),((6789144069:ℚ)/10000000000),((-4709144069:ℚ)/12400000000),((-1920563179:ℚ)/6740000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2615004323:ℚ)/5000000000),((43219336185136147442816200759855401597492859423188171637:ℚ)/177968301450000000000000000000000000000000000000000000000),((72870523519703270104206191:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((3352081033:ℚ)/5000000000),((1381838393:ℚ)/2000000000),((-321946131:ℚ)/842500000),((-14824567231:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4904381111:ℚ)/10000000000),((209742751337544574942875362330496999011701633653237225881839:ℚ)/863083591406250000000000000000000000000000000000000000000000),((432645839671789016394567279:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6824209623:ℚ)/10000000000),((1393839567:ℚ)/2000000000),((-977839567:ℚ)/2575000000),((-10163155787:ℚ)/34650000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((45577013:ℚ)/100000000),((4825431926360736997694000386828399713789755109407599199453:ℚ)/20085757834570312500000000000000000000000000000000000000000),((1638654511917022302807420719:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((215131729:ℚ)/312500000),((7029192099:ℚ)/10000000000),((-4949192099:ℚ)/12993750000),((-965922103:ℚ)/3278125000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4374902689:ℚ)/10000000000),((2500503759193309283508281115629391291364435599981287713:ℚ)/10402994282770156860351562500000000000000000000000000000),((1555086716215444178635551:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((694420943:ℚ)/1000000000),((1772293769:ℚ)/2500000000),((-1252293769:ℚ)/3278125000),((-3132946601:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((836939891:ℚ)/2000000000),((1869902555806802913394271209642531473685218713507620010411:ℚ)/7775495826591406250000000000000000000000000000000000000000),((15459753675612366938643039:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((7004192249:ℚ)/10000000000),((7149147073:ℚ)/10000000000),((-5069147073:ℚ)/13231250000),((-31749345743:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((498253329:ℚ)/1250000000),((969544208229968435773393572873814878883013783962543607202121:ℚ)/4029532307100000000000000000000000000000000000000000000000000),((1499354087235627479889741711:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((706416409:ℚ)/1000000000),((7209108387:ℚ)/10000000000),((-5129108387:ℚ)/13350000000),((-3216914863:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3777542847:ℚ)/10000000000),((1963081824024649582714223898265592980690743705006428791:ℚ)/8154609144973754882812500000000000000000000000000000000),((40236698858533612400631:ℚ)/409600000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7124125251:ℚ)/10000000000),((3634529651:ℚ)/5000000000),((-2594529651:ℚ)/6734375000),((-32588876757:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3557518117:ℚ)/10000000000),((833304013434440432717126549765099690958387171724001034605097:ℚ)/3459759573706250000000000000000000000000000000000000000000000),((1405547466079512131414726711:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((449004751:ℚ)/625000000),((229031253:ℚ)/312500000),((-164031253:ℚ)/424609375),((-2063033257:ℚ)/6853125000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((166182771:ℚ)/500000000),((43911068441072906180034726052618248083440587224676053863:ℚ)/182219258673334121704101562500000000000000000000000000000),((14698340980555752009351:ℚ)/160000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3622008331:ℚ)/5000000000),((923616379:ℚ)/1250000000),((-663616379:ℚ)/1713281250),((-16714058317:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((768197673:ℚ)/2500000000),((2910679936001647069185667881408361496205755561312789804413:ℚ)/12072377694042968750000000000000000000000000000000000000000),((327746988375216478241516871:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((7303947453:ℚ)/10000000000),((117324443:ℚ)/156250000),((-84824443:ℚ)/216015625),((-3760848019:ℚ)/12500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2800351731:ℚ)/10000000000),((19295937355434266747049204381139549134968727119981134099:ℚ)/79107284545898437500000000000000000000000000000000000000),((3499793838967029072243359:ℚ)/40960000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((7423780491:ℚ)/10000000000),((7628561211:ℚ)/10000000000),((-5548561211:ℚ)/14062500000),((-34686463437:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((86305393:ℚ)/400000000),((20558233535685708969376452726472291626400215122230370673743:ℚ)/84217161600000000000000000000000000000000000000000000000000),((3234723091183228405776431:ℚ)/40960000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((1885894269:ℚ)/2500000000),((1073227349:ℚ)/1250000000),((-73929759:ℚ)/162500000),((-2960419961:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((121928449:ℚ)/1000000000),((9505163230871943226096020062621051430319051661340613829:ℚ)/34117200000000000000000000000000000000000000000000000000),((66955590083108391239103671:ℚ)/924160000000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((850083277:ℚ)/1000000000),((5248081961:ℚ)/5000000000),((-1402693987:ℚ)/2700000000),((-4222582939:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((212332832921165833229144378090791763654618595152365450987:ℚ)/691200000000000000000000000000000000000000000000000000000),((14204889:ℚ)/204800000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10411175217:ℚ)/10000000000),((14308267867:ℚ)/10000000000),((-12228267867:ℚ)/20000000000),((-18532742173:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((668029936159645713383879410056609505203630170498118116269:ℚ)/1868851200000000000000000000000000000000000000000000000000),((14204889:ℚ)/204800000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((45:ℚ)/64) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC09
#check @N11Formalization.C450Source28GroupedC09.bound
#print axioms N11Formalization.C450Source28GroupedC09.valid0
#print axioms N11Formalization.C450Source28GroupedC09.valid1
#print axioms N11Formalization.C450Source28GroupedC09.valid2
#print axioms N11Formalization.C450Source28GroupedC09.valid3
#print axioms N11Formalization.C450Source28GroupedC09.valid4
#print axioms N11Formalization.C450Source28GroupedC09.valid5
#print axioms N11Formalization.C450Source28GroupedC09.valid6
#print axioms N11Formalization.C450Source28GroupedC09.valid7
#print axioms N11Formalization.C450Source28GroupedC09.valid8
#print axioms N11Formalization.C450Source28GroupedC09.valid9
#print axioms N11Formalization.C450Source28GroupedC09.valid10
#print axioms N11Formalization.C450Source28GroupedC09.valid11
#print axioms N11Formalization.C450Source28GroupedC09.valid12
#print axioms N11Formalization.C450Source28GroupedC09.valid13
#print axioms N11Formalization.C450Source28GroupedC09.valid14
#print axioms N11Formalization.C450Source28GroupedC09.bound
#print axioms N11Formalization.C450Source28GroupedC09.endpoint_checks
