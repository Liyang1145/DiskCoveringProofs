import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6733264769:ℚ)/10000000000),((1735043821:ℚ)/2500000000),((-15405482031:ℚ)/24800000000),((-5197264769:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2411226117:ℚ)/5000000000),((24560270207605437892210267964788477417264634088084905349497509:ℚ)/97440021475200000000000000000000000000000000000000000000000000),((1129284027507218638449340243:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1713201069:ℚ)/2500000000),((6999911557:ℚ)/10000000000),((-20759675709:ℚ)/33700000000),((-1329201069:ℚ)/2551250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((1117865301:ℚ)/2500000000),((153996623899906567001713440882994709222450515928479205541679:ℚ)/622781562460128906250000000000000000000000000000000000000000),((210591539222118397729287329:ℚ)/554496000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((3456281449:ℚ)/5000000000),((3529820553:ℚ)/5000000000),((-2420617391:ℚ)/3925000000),((-2688281449:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4286017521:ℚ)/10000000000),((991923774666506111500183941563698501666171815881641345829:ℚ)/4009345198925781250000000000000000000000000000000000000000),((280014258230658647827103363:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((11155703:ℚ)/16000000),((7119364117:ℚ)/10000000000),((-63593005287:ℚ)/103000000000),((-8698103:ℚ)/16632000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4092744659:ℚ)/10000000000),((260955691881638141037110286059133200129690774344290673046252179:ℚ)/1054247643126562500000000000000000000000000000000000000000000000),((2859358742188692313667:ℚ)/7570718720000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7032058907:ℚ)/10000000000),((1787305807:ℚ)/2500000000),((-5326787959:ℚ)/8662500000),((-5496058907:ℚ)/10442500000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((778094267:ℚ)/2000000000),((131696435092631718293080064476756950835998249863023659038557:ℚ)/536988245859805297851562500000000000000000000000000000000000),((1113794800618845802622199387:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((7061928629:ℚ)/10000000000),((7179080771:ℚ)/10000000000),((-64249888481:ℚ)/104425000000),((-5525928629:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3785509701:ℚ)/10000000000),((480308866818243518417884168725765630530886915808891663655728339:ℚ)/1957872715602696118164062500000000000000000000000000000000000000),((1112215376930848043689085883:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((1418359337:ℚ)/2000000000),((112639637:ℚ)/156250000),((-1009036007:ℚ)/1639062500),((-1111159337:ℚ)/2107500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((57464187:ℚ)/156250000),((47993466922024439540005442504504813038869142608055769857:ℚ)/195578769419479608535766601562500000000000000000000000000),((44425216259419903933849347:ℚ)/118292480000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3560831549:ℚ)/5000000000),((180969781:ℚ)/250000000),((-540889197:ℚ)/878125000),((-2792831549:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((142672321:ℚ)/400000000),((4655569746589410512984134858366953045583963563032376830367:ℚ)/18966655594110298156738281250000000000000000000000000000000),((277259972249665266913990763:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((1787881973:ℚ)/2500000000),((7268644207:ℚ)/10000000000),((-65235086277:ℚ)/105850000000),((-1403881973:ℚ)/2658125000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3452510697:ℚ)/10000000000),((32918842831170482830589017659650739297203800112965002399978647007:ℚ)/134073630591847278906250000000000000000000000000000000000000000000),((69215239007203810977178427:ℚ)/184832000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((7181391087:ℚ)/10000000000),((7298495691:ℚ)/10000000000),((-65563452601:ℚ)/106325000000),((-1881797029:ℚ)/3560000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3334466007:ℚ)/10000000000),((3653625303688690710203545575433441409891220512759104263498611:ℚ)/14876686580471606445312500000000000000000000000000000000000000),((3317526635030894510229366041:ℚ)/8871936000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((1442250541:ℚ)/2000000000),((732834571:ℚ)/1000000000),((-2196393427:ℚ)/3560000000),((-1135050541:ℚ)/2145500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((1606130097:ℚ)/5000000000),((2847088425107292102948538052370099231636734318667550268679:ℚ)/11589615457043750000000000000000000000000000000000000000000),((44169402056098895721227403:ℚ)/118292480000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((113142387:ℚ)/156250000),((1471638857:ℚ)/2000000000),((-13244027427:ℚ)/21455000000),((-89142387:ℚ)/168359375),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3085398177:ℚ)/10000000000),((11005855113113033841931475275851371902939927558822908082233:ℚ)/44789905789853305053710937500000000000000000000000000000000),((807584723872439905027841:ℚ)/2166000000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((7270971297:ℚ)/10000000000),((7417887177:ℚ)/10000000000),((-66876758947:ℚ)/107750000000),((-5734971297:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1476639633:ℚ)/5000000000),((2291775179343324205541277029884627577993472177810832904706442817:ℚ)/9238276192663964843750000000000000000000000000000000000000000000),((3303012258572292969336787001:ℚ)/8871936000000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7330683831:ℚ)/10000000000),((7477574517:ℚ)/10000000000),((-67533319687:ℚ)/108700000000),((-1931561277:ℚ)/3655000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2670117137:ℚ)/10000000000),((266127750644236623780065712115362725022336152714021882745132093:ℚ)/1072366928982160937500000000000000000000000000000000000000000000),((3293252779826077307956915529:ℚ)/8871936000000000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((1847597617:ℚ)/2500000000),((150745129:ℚ)/200000000),((-1363796419:ℚ)/2193000000),((-1463597617:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2354056937:ℚ)/10000000000),((11170501828703588586719686516248539082035942623040773807:ℚ)/44995404561636621093750000000000000000000000000000000000),((68404723165518140617313907:ℚ)/184832000000000000000000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7450091361:ℚ)/10000000000),((777593283:ℚ)/1000000000),((-7081526113:ℚ)/11060000000),((-5914091361:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((248684093:ℚ)/1250000000),((3477915053133368779730494987896622742990081896936482390071:ℚ)/13300688451050000000000000000000000000000000000000000000000),((3273534049504320792345994169:ℚ)/8871936000000000000000000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7688840381:ℚ)/10000000000),((109124303:ℚ)/125000000),((-1016367333:ℚ)/1430000000),((-6152840381:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((952801772052045480711566320505617492021710496271296273:ℚ)/3074634956250000000000000000000000000000000000000000000),((374930277:ℚ)/1024000000)⟩
theorem valid16 : Valid source25 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((540193701:ℚ)/625000000),((5317835203:ℚ)/5000000000),((-51136187233:ℚ)/64800000000),((-444193701:ℚ)/1000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((609196938172660743948536343858958483533455521937688738187:ℚ)/1700611200000000000000000000000000000000000000000000000000),((374930277:ℚ)/1024000000)⟩
theorem valid17 : Valid source25 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((2637294477:ℚ)/2500000000),((7221190029:ℚ)/5000000000),((-72073090319:ℚ)/80000000000),((-751098159:ℚ)/1840000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((30120575160709666686828651920745139494823:ℚ)/67712000000000000000000000000000000000000),((374930277:ℚ)/1024000000)⟩
theorem valid18 : Valid source25 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source25 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source25 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source25 nn0 nn1 Qcell ((4291:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC06
#check @N11Formalization.C450Source25GroupedC06.bound
#print axioms N11Formalization.C450Source25GroupedC06.valid0
#print axioms N11Formalization.C450Source25GroupedC06.valid1
#print axioms N11Formalization.C450Source25GroupedC06.valid2
#print axioms N11Formalization.C450Source25GroupedC06.valid3
#print axioms N11Formalization.C450Source25GroupedC06.valid4
#print axioms N11Formalization.C450Source25GroupedC06.valid5
#print axioms N11Formalization.C450Source25GroupedC06.valid6
#print axioms N11Formalization.C450Source25GroupedC06.valid7
#print axioms N11Formalization.C450Source25GroupedC06.valid8
#print axioms N11Formalization.C450Source25GroupedC06.valid9
#print axioms N11Formalization.C450Source25GroupedC06.valid10
#print axioms N11Formalization.C450Source25GroupedC06.valid11
#print axioms N11Formalization.C450Source25GroupedC06.valid12
#print axioms N11Formalization.C450Source25GroupedC06.valid13
#print axioms N11Formalization.C450Source25GroupedC06.valid14
#print axioms N11Formalization.C450Source25GroupedC06.valid15
#print axioms N11Formalization.C450Source25GroupedC06.valid16
#print axioms N11Formalization.C450Source25GroupedC06.valid17
#print axioms N11Formalization.C450Source25GroupedC06.valid18
#print axioms N11Formalization.C450Source25GroupedC06.bound
#print axioms N11Formalization.C450Source25GroupedC06.endpoint_checks
