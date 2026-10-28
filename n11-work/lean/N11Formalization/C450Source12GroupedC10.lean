import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((3169450677:ℚ)/5000000000),((6617829761:ℚ)/10000000000),((-39924808327:ℚ)/99200000000),((-7748352031:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((730448539:ℚ)/1250000000),((7527550890794608551007947574709985541968374294391869183:ℚ)/206753765869140625000000000000000000000000000000000000000),((302581167776348262183608247:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6576811513:ℚ)/10000000000),((6855763561:ℚ)/10000000000),((-41590344927:ℚ)/103000000000),((-16210434539:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((524908227:ℚ)/1000000000),((6168336381932520082942256654072169411988980467559635699:ℚ)/170183922656250000000000000000000000000000000000000000000),((298348863154493788347633447:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3407346207:ℚ)/5000000000),((3487359529:ℚ)/5000000000),((-21211516703:ℚ)/53400000000),((-8462038621:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4586069849:ℚ)/10000000000),((74012354978171326126503501619805417599569307540156376881:ℚ)/2093051692510986328125000000000000000000000000000000000000),((73500507022709487698789287:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3466811427:ℚ)/5000000000),((7034194129:ℚ)/10000000000),((-42839358903:ℚ)/108700000000),((-8640434281:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2109423701:ℚ)/5000000000),((2830159550534324039525890369585635837005318009489020163:ℚ)/80986337188148498535156250000000000000000000000000000000),((291829578402088655094276887:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((1748271431:ℚ)/2500000000),((1773416869:ℚ)/2500000000),((-3604639361:ℚ)/9137500000),((-623544899:ℚ)/1975000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4023511751:ℚ)/10000000000),((1200538342435656639974020520526400818789276872041543:ℚ)/34371519947052001953125000000000000000000000000000000),((18173414818861458606746527:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3526273541:ℚ)/5000000000),((1430627829:ℚ)/2000000000),((-8734394803:ℚ)/22120000000),((-8818820623:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3818771641:ℚ)/10000000000),((10222486695689766523883330863514928707001327423471695617:ℚ)/292815413104200363159179687500000000000000000000000000000),((34766429289860414712827261:ℚ)/354877440000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((1422401393:ℚ)/2000000000),((3591437181:ℚ)/5000000000),((-21940060267:ℚ)/55775000000),((-3563204179:ℚ)/11202500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3603020117:ℚ)/10000000000),((1701341218786921147562981618977433922306806392617948203:ℚ)/49007715021013427734375000000000000000000000000000000000),((216476125737247385613295181:ℚ)/2217984000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((3570868183:ℚ)/5000000000),((901576147:ℚ)/1250000000),((-5511033029:ℚ)/14003125000),((-8952604549:ℚ)/28125000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((174518989:ℚ)/500000000),((1759910851908267040260527707603999645250269957712988769:ℚ)/50705065950751304626464843750000000000000000000000000000),((4501687292757697201462863:ℚ)/46208000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((1792866353:ℚ)/2500000000),((7242343591:ℚ)/10000000000),((-4921822793:ℚ)/12500000000),((-4498599059:ℚ)/14121875000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((421767651:ℚ)/1250000000),((38175990295277696712168759947004355506462452499907613:ℚ)/1100112561690807342529296875000000000000000000000000000),((287581275794883697935479367:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1800298527:ℚ)/2500000000),((7272077613:ℚ)/10000000000),((-44504543291:ℚ)/112975000000),((-4520895581:ℚ)/14181250000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((813479563:ℚ)/2500000000),((436671135523855436153662153749244254979544619878772893:ℚ)/12585947747605085372924804687500000000000000000000000000),((45324426536648385642833471:ℚ)/466944000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((3615461229:ℚ)/5000000000),((3665772247:ℚ)/5000000000),((-22460405729:ℚ)/56725000000),((-9086383687:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3129251147:ℚ)/10000000000),((722857048534291376409460993529048454600166144790395464341:ℚ)/20734455259375000000000000000000000000000000000000000000000),((71640086921094664240266663:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7290378139:ℚ)/10000000000),((3695504929:ℚ)/5000000000),((-22668534503:ℚ)/57200000000),((-18351134417:ℚ)/57675000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((286424107:ℚ)/1000000000),((4862612095734383368451588379039917537380603348251071:ℚ)/139539660402059555053710937500000000000000000000000000),((71377035206176595637421687:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((918729061:ℚ)/1250000000),((7450473743:ℚ)/10000000000),((-45753316201:ℚ)/115350000000),((-2316187183:ℚ)/7268750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((257289587:ℚ)/1000000000),((12055277955528674297413917914926381077677237487682695043:ℚ)/346088226540470123291015625000000000000000000000000000000),((14971393624726668888909997:ℚ)/155648000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((3704642769:ℚ)/5000000000),((236543663:ℚ)/312500000),((-1455805641:ℚ)/3634375000),((-9353928307:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1122489817:ℚ)/5000000000),((3815324846256330505639157426333959922540662397919607101:ℚ)/108539658190917968750000000000000000000000000000000000000),((276827616402118914103083:ℚ)/2888000000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((1882046967:ℚ)/2500000000),((97590349:ℚ)/125000000),((-603132443:ℚ)/1477500000),((-4766140901:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((171972771:ℚ)/1250000000),((479915575812781253667061417348459069901533867137841673:ℚ)/13422308349609375000000000000000000000000000000000000000),((23130949885953077:ℚ)/243200000000000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((7765978267:ℚ)/10000000000),((8282831037:ℚ)/10000000000),((-51579817259:ℚ)/122000000000),((-19777934801:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8847749849169314913851755675546918246776188262175472929:ℚ)/240132600000000000000000000000000000000000000000000000000),((96926417:ℚ)/1024000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((2060376973:ℚ)/2500000000),((10184669749:ℚ)/10000000000),((-21630896081:ℚ)/43200000000),((-5301130919:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3581398589311562379694622817555332266487718563522440099:ℚ)/84375000000000000000000000000000000000000000000000000000),((96926417:ℚ)/1024000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((10143122633:ℚ)/10000000000),((13986826961:ℚ)/10000000000),((-91507788727:ℚ)/160000000000),((-26909367899:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2125322602658117019134380051036792572057947330226295639:ℚ)/43801200000000000000000000000000000000000000000000000000),((96926417:ℚ)/1024000000)⟩
theorem valid17 : Valid source12 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC10
#check @N11Formalization.C450Source12GroupedC10.bound
#print axioms N11Formalization.C450Source12GroupedC10.valid0
#print axioms N11Formalization.C450Source12GroupedC10.valid1
#print axioms N11Formalization.C450Source12GroupedC10.valid2
#print axioms N11Formalization.C450Source12GroupedC10.valid3
#print axioms N11Formalization.C450Source12GroupedC10.valid4
#print axioms N11Formalization.C450Source12GroupedC10.valid5
#print axioms N11Formalization.C450Source12GroupedC10.valid6
#print axioms N11Formalization.C450Source12GroupedC10.valid7
#print axioms N11Formalization.C450Source12GroupedC10.valid8
#print axioms N11Formalization.C450Source12GroupedC10.valid9
#print axioms N11Formalization.C450Source12GroupedC10.valid10
#print axioms N11Formalization.C450Source12GroupedC10.valid11
#print axioms N11Formalization.C450Source12GroupedC10.valid12
#print axioms N11Formalization.C450Source12GroupedC10.valid13
#print axioms N11Formalization.C450Source12GroupedC10.valid14
#print axioms N11Formalization.C450Source12GroupedC10.valid15
#print axioms N11Formalization.C450Source12GroupedC10.valid16
#print axioms N11Formalization.C450Source12GroupedC10.valid17
#print axioms N11Formalization.C450Source12GroupedC10.bound
#print axioms N11Formalization.C450Source12GroupedC10.endpoint_checks
