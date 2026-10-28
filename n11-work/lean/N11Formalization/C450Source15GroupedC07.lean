import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((80969691:ℚ)/125000000),((6772640133:ℚ)/10000000000),((-5940640133:ℚ)/9920000000),((-616727219:ℚ)/1287500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2752027171:ℚ)/5000000000),((3478670433167869496107154417794563127658003572837948970867:ℚ)/64727596851200000000000000000000000000000000000000000000000),((13557490088210272943931:ℚ)/57760000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1678906789:ℚ)/2500000000),((430728743:ℚ)/625000000),((-378728743:ℚ)/643750000),((-12870161101:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4872256291:ℚ)/10000000000),((23719795267709145747452609460173506804903605131753892177:ℚ)/458693650637435913085937500000000000000000000000000000000),((5399186230823461251646971:ℚ)/23104000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((6834638051:ℚ)/10000000000),((3505335007:ℚ)/5000000000),((-3089335007:ℚ)/5245000000),((-52551742459:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4526426901:ℚ)/10000000000),((831594765314414507930349687948398279024973066241741917313:ℚ)/16072336864562695312500000000000000000000000000000000000000),((86195779597435457647631051:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((6953639633:ℚ)/10000000000),((56561373:ℚ)/80000000),((-49905373:ℚ)/85440000),((-53622756697:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4154059177:ℚ)/10000000000),((47902884224136812627363358377577481424180094740201:ℚ)/942881374144800000000000000000000000000000000000000),((86004097408299655252582739:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7013137087:ℚ)/10000000000),((7129671017:ℚ)/10000000000),((-6297671017:ℚ)/10775000000),((-54158233783:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((494449129:ℚ)/1250000000),((469557901599754450023564627423676389204497507696853006993343:ℚ)/9238276192663964843750000000000000000000000000000000000000000),((85908075314255584915109619:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((3536316197:ℚ)/5000000000),((3579709949:ℚ)/5000000000),((-3163709949:ℚ)/5435000000),((-27346845773:ℚ)/54587500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((1873608419:ℚ)/5000000000),((60250064998483874970611382780637693954964811059880343551699:ℚ)/1195983157716873388671875000000000000000000000000000000000000),((21452983111722101638244859:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((355118963:ℚ)/500000000),((3594584123:ℚ)/5000000000),((-288962193:ℚ)/496250000),((-2748070667:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((727756469:ℚ)/2000000000),((46274759371631937943380496851321315005791502561612217527:ℚ)/918330161985708618164062500000000000000000000000000000000),((214409539247233533469419:ℚ)/924160000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((713212561:ℚ)/1000000000),((1804729017:ℚ)/2500000000),((-1596729017:ℚ)/2741250000),((-5522913049:ℚ)/11012500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((1763585191:ℚ)/5000000000),((139904117424990004713540770301876777052000610950580600807:ℚ)/2775717525297097778320312500000000000000000000000000000000),((857156687289780551625171:ℚ)/3696640000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7161871451:ℚ)/10000000000),((7248663369:ℚ)/10000000000),((-6416663369:ℚ)/11012500000),((-7928120437:ℚ)/15800000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1706034303:ℚ)/5000000000),((164147478150599769131131071595087642155083466371133376311:ℚ)/3255906925720977783203125000000000000000000000000000000000),((85667491527417450612057851:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7191616789:ℚ)/10000000000),((3639205079:ℚ)/5000000000),((-3223205079:ℚ)/5530000000),((-55764551101:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((823277637:ℚ)/2500000000),((263035540313451199428781356109183021196986883284557437281169:ℚ)/5216125673377926562500000000000000000000000000000000000000000),((85619284086078652559026971:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7221361631:ℚ)/10000000000),((182703911:ℚ)/250000000),((-161903911:ℚ)/277687500),((-56032254679:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3169861503:ℚ)/10000000000),((7466264529719313052377324932374317782654286381527148353:ℚ)/148025192962421273803710937500000000000000000000000000000),((85571046395181392777154611:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((7251105983:ℚ)/10000000000),((920955939:ℚ)/1250000000),((-816955939:ℚ)/1394375000),((-56299953847:ℚ)/112500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3041799327:ℚ)/10000000000),((69866631568674067946199731208006320240642987764210451:ℚ)/1372472967027282714843750000000000000000000000000000000),((236905203453017804552699:ℚ)/1024000000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1827648311:ℚ)/2500000000),((7427136633:ℚ)/10000000000),((-6595136633:ℚ)/11250000000),((-14208834799:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((34606719:ℚ)/125000000),((648055514419107947734862581272426558202542462631675172183:ℚ)/12726356231689453125000000000000000000000000000000000000000),((5339134483642180770899171:ℚ)/23104000000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7370078619:ℚ)/10000000000),((3743311927:ℚ)/5000000000),((-3327311927:ℚ)/5672500000),((-57370707571:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1233016521:ℚ)/5000000000),((594137022123122513156982413549901012628221440371414849449:ℚ)/11663948952536181640625000000000000000000000000000000000000),((85329403896902168418271611:ℚ)/369664000000000000000000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1857390539:ℚ)/2500000000),((7605592781:ℚ)/10000000000),((-6773592781:ℚ)/11440000000),((-14476514851:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2121808579:ℚ)/10000000000),((59630912837893815001458665691928082284628239937893882727689:ℚ)/1150601232809600000000000000000000000000000000000000000000000),((5327033428500996297066971:ℚ)/23104000000000000000000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((943565487:ℚ)/1250000000),((154491093:ℚ)/200000000),((-137851093:ℚ)/232600000),((-7372089383:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1164545527:ℚ)/10000000000),((39553482753864961493787183266209091739581437440807907:ℚ)/763100274041537500000000000000000000000000000000000000),((1328725514495005354731219:ℚ)/5776000000000000000000000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((7667478811:ℚ)/10000000000),((7962458541:ℚ)/10000000000),((-7130458541:ℚ)/11820000000),((-60047309299:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((684751133577839644252824251814074356140128134261783502713:ℚ)/12801794819850000000000000000000000000000000000000000000000),((5883261:ℚ)/25600000)⟩
theorem valid16 : Valid source15 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7905369447:ℚ)/10000000000),((263693597:ℚ)/312500000),((-237693597:ℚ)/381250000),((-62188325023:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2055270856012459610807349470766961657762155276370872347:ℚ)/36357967309570312500000000000000000000000000000000000000),((5883261:ℚ)/25600000)⟩
theorem valid17 : Valid source15 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4190540921:ℚ)/5000000000),((10340440433:ℚ)/10000000000),((-9508440433:ℚ)/12960000000),((-33234868289:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((330183251270376381697359369593985961764175883858219861:ℚ)/4534963200000000000000000000000000000000000000000000000),((5883261:ℚ)/25600000)⟩
theorem valid18 : Valid source15 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((2056650707:ℚ)/2000000000),((883942147:ℚ)/625000000),((-831942147:ℚ)/1000000000),((-16717856363:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((667514203351572031606947274632859280953126440684715237:ℚ)/7439062500000000000000000000000000000000000000000000000),((5883261:ℚ)/25600000)⟩
theorem valid19 : Valid source15 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4443:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4443:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((4443:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC07
#check @N11Formalization.C450Source15GroupedC07.bound
#print axioms N11Formalization.C450Source15GroupedC07.valid0
#print axioms N11Formalization.C450Source15GroupedC07.valid1
#print axioms N11Formalization.C450Source15GroupedC07.valid2
#print axioms N11Formalization.C450Source15GroupedC07.valid3
#print axioms N11Formalization.C450Source15GroupedC07.valid4
#print axioms N11Formalization.C450Source15GroupedC07.valid5
#print axioms N11Formalization.C450Source15GroupedC07.valid6
#print axioms N11Formalization.C450Source15GroupedC07.valid7
#print axioms N11Formalization.C450Source15GroupedC07.valid8
#print axioms N11Formalization.C450Source15GroupedC07.valid9
#print axioms N11Formalization.C450Source15GroupedC07.valid10
#print axioms N11Formalization.C450Source15GroupedC07.valid11
#print axioms N11Formalization.C450Source15GroupedC07.valid12
#print axioms N11Formalization.C450Source15GroupedC07.valid13
#print axioms N11Formalization.C450Source15GroupedC07.valid14
#print axioms N11Formalization.C450Source15GroupedC07.valid15
#print axioms N11Formalization.C450Source15GroupedC07.valid16
#print axioms N11Formalization.C450Source15GroupedC07.valid17
#print axioms N11Formalization.C450Source15GroupedC07.valid18
#print axioms N11Formalization.C450Source15GroupedC07.valid19
#print axioms N11Formalization.C450Source15GroupedC07.bound
#print axioms N11Formalization.C450Source15GroupedC07.endpoint_checks
