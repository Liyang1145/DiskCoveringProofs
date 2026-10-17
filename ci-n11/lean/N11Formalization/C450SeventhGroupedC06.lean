import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((158075849:ℚ)/250000000),((6600140347:ℚ)/10000000000),((-69401543817:ℚ)/99200000000),((-148475849:ℚ)/257500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((45947863:ℚ)/78125000),((385011109615622737227144202505629143894664309227980287343057:ℚ)/32363798425600000000000000000000000000000000000000000000000000),((5638201836876449791566657:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((1312121303:ℚ)/2000000000),((3418862167:ℚ)/5000000000),((-36007483837:ℚ)/51500000000),((-1235321303:ℚ)/2136000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5291475493:ℚ)/10000000000),((90350754371552290744279988529247089547762946764491348852917:ℚ)/7607364756152343750000000000000000000000000000000000000000000),((1410655918762020744937697:ℚ)/11552000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1359634781:ℚ)/2000000000),((1739128531:ℚ)/2500000000),((-6110137947:ℚ)/8900000000),((-1282834781:ℚ)/2174000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((463492457:ℚ)/1000000000),((29495272025378154903471502637414043555600635328541807748787:ℚ)/2603029738628125000000000000000000000000000000000000000000000),((352751956035667987657103:ℚ)/2888000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((864619479:ℚ)/1250000000),((3507954251:ℚ)/5000000000),((-36987496761:ℚ)/54350000000),((-272206493:ℚ)/456875000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4272088239:ℚ)/10000000000),((742212373596814761861686743129546536206515738273232706977121:ℚ)/67022933061385058593750000000000000000000000000000000000000000),((1411188908609188272418273:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((6976346381:ℚ)/10000000000),((7075302547:ℚ)/10000000000),((-24876109339:ℚ)/36550000000),((-6592346381:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((815878479:ℚ)/2000000000),((24231060848013718334648811797446073486301679971598595263297:ℚ)/2187276610635113525390625000000000000000000000000000000000000),((5645936330949623829123057:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3517868331:ℚ)/5000000000),((7104999447:ℚ)/10000000000),((-74954993917:ℚ)/110600000000),((-1108622777:ℚ)/1851250000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((193884677:ℚ)/500000000),((76186776250934341685401853928818195822742611281413242496874039:ℚ)/6954834231170568750000000000000000000000000000000000000000000000),((16938931414268369444502571:ℚ)/138624000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1413086341:ℚ)/2000000000),((7134696267:ℚ)/10000000000),((-75281658937:ℚ)/111075000000),((-1336286341:ℚ)/2231000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((188650907:ℚ)/500000000),((14597388886693977490350461310941074464762648978869628483373897:ℚ)/1332226736661791464233398437500000000000000000000000000000000000),((16940728106620560658146691:ℚ)/138624000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7095126683:ℚ)/10000000000),((447774563:ℚ)/625000000),((-4725520193:ℚ)/6971875000),((-6711126683:ℚ)/11202500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((733100377:ℚ)/2000000000),((9321956068325339519856961798983045992634755058310034962993:ℚ)/850567289125984767913818359375000000000000000000000000000000),((176484740181296556299421:ℚ)/1444000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((3562410799:ℚ)/5000000000),((7194089671:ℚ)/10000000000),((-75934986381:ℚ)/112025000000),((-3370410799:ℚ)/5625000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((142195461:ℚ)/400000000),((15238310654037595413454937082997338781022795929984007101:ℚ)/1390080442032051086425781250000000000000000000000000000000),((5648117422192396285224793:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((143090329:ℚ)/200000000),((451486641:ℚ)/625000000),((-4766353051:ℚ)/7031250000),((-135410329:ℚ)/225950000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((688174537:ℚ)/2000000000),((81078124487060155640296086586872627701606404203203854099153:ℚ)/7394538407027721405029296875000000000000000000000000000000000),((264784058344653848846281:ℚ)/2166000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7184211241:ℚ)/10000000000),((3626741383:ℚ)/5000000000),((-38294155213:ℚ)/56487500000),((-6800211241:ℚ)/11345000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((664622011:ℚ)/2000000000),((79506330860929357037885902027851316615977172476970903712453:ℚ)/7249634058520379623413085937500000000000000000000000000000000),((1412334788331174627174097:ℚ)/11552000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((721390597:ℚ)/1000000000),((7283179201:ℚ)/10000000000),((-76914971211:ℚ)/113450000000),((-682990597:ℚ)/1139250000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3201184409:ℚ)/10000000000),((1039435438486446320510270084048907095827702099124066230262788651:ℚ)/94759242318609430078125000000000000000000000000000000000000000000),((5649955148090178538898473:ℚ)/46208000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7243600639:ℚ)/10000000000),((7312875561:ℚ)/10000000000),((-77241631171:ℚ)/113925000000),((-6859600639:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((76864999:ℚ)/250000000),((3040103987532863349621563889271282749010534165058535646679:ℚ)/277092537254736328125000000000000000000000000000000000000000),((16951723686824683083111499:ℚ)/138624000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7273295249:ℚ)/10000000000),((917821481:ℚ)/1250000000),((-9696036291:ℚ)/14300000000),((-6889295249:ℚ)/11487500000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((2942754983:ℚ)/10000000000),((84691112020867142270380809206748644836870205050890276081339:ℚ)/7717722462896875000000000000000000000000000000000000000000000),((176599918621951263194481:ℚ)/1444000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((36514949:ℚ)/50000000),((7372268063:ℚ)/10000000000),((-77894948693:ℚ)/114875000000),((-34594949:ℚ)/57675000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((70122679:ℚ)/250000000),((10809684223877808146801346662230006726543477043185141552277:ℚ)/984876599010513067245483398437500000000000000000000000000000),((5651823648976187014362537:ℚ)/46208000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1833171073:ℚ)/2500000000),((3715830139:ℚ)/5000000000),((-39274131529:ℚ)/57675000000),((-1737171073:ℚ)/2907500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1330061409:ℚ)/5000000000),((2999844099944121046999165383837926128924374200504304123731363:ℚ)/270303087251303173828125000000000000000000000000000000000000000),((1413326936344086040329633:ℚ)/11552000000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((3696036553:ℚ)/5000000000),((7550443879:ℚ)/10000000000),((-79854882669:ℚ)/116300000000),((-3504036553:ℚ)/5910000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2344545619:ℚ)/10000000000),((540715039615684940748672180542555063920872399199574717335661:ℚ)/47693767127596093750000000000000000000000000000000000000000000),((5656316967452685111427993:ℚ)/46208000000000000000000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((7510850067:ℚ)/10000000000),((7788007939:ℚ)/10000000000),((-27489362443:ℚ)/39400000000),((-7126850067:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((306636717:ℚ)/2000000000),((25165038637080402136241234348299183156733078225705925562081:ℚ)/2133632469975000000000000000000000000000000000000000000000000),((119092377718336427:ℚ)/972800000000000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7748401469:ℚ)/10000000000),((1652624957:ℚ)/2000000000),((-17538874527:ℚ)/24400000000),((-7364401469:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3763419841680485422593878487545537084322402896994389415103:ℚ)/297844468200000000000000000000000000000000000000000000000000),((15668209:ℚ)/128000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((2055873807:ℚ)/2500000000),((10163481137:ℚ)/10000000000),((-108598292507:ℚ)/129600000000),((-1959873807:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((350674651915565779988295235627852722236286985099473290369:ℚ)/20407334400000000000000000000000000000000000000000000000000),((15668209:ℚ)/128000000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((10123781173:ℚ)/10000000000),((2792779883:ℚ)/2000000000),((-30080578713:ℚ)/32000000000),((-9739781173:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((426258965432753974884129035814597286291:ℚ)/19501056000000000000000000000000000000000),((15668209:ℚ)/128000000)⟩
theorem valid20 : Valid seventh packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4519:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC06
#check @N11Formalization.C450SeventhGroupedC06.bound
#print axioms N11Formalization.C450SeventhGroupedC06.valid0
#print axioms N11Formalization.C450SeventhGroupedC06.valid1
#print axioms N11Formalization.C450SeventhGroupedC06.valid2
#print axioms N11Formalization.C450SeventhGroupedC06.valid3
#print axioms N11Formalization.C450SeventhGroupedC06.valid4
#print axioms N11Formalization.C450SeventhGroupedC06.valid5
#print axioms N11Formalization.C450SeventhGroupedC06.valid6
#print axioms N11Formalization.C450SeventhGroupedC06.valid7
#print axioms N11Formalization.C450SeventhGroupedC06.valid8
#print axioms N11Formalization.C450SeventhGroupedC06.valid9
#print axioms N11Formalization.C450SeventhGroupedC06.valid10
#print axioms N11Formalization.C450SeventhGroupedC06.valid11
#print axioms N11Formalization.C450SeventhGroupedC06.valid12
#print axioms N11Formalization.C450SeventhGroupedC06.valid13
#print axioms N11Formalization.C450SeventhGroupedC06.valid14
#print axioms N11Formalization.C450SeventhGroupedC06.valid15
#print axioms N11Formalization.C450SeventhGroupedC06.valid16
#print axioms N11Formalization.C450SeventhGroupedC06.valid17
#print axioms N11Formalization.C450SeventhGroupedC06.valid18
#print axioms N11Formalization.C450SeventhGroupedC06.valid19
#print axioms N11Formalization.C450SeventhGroupedC06.valid20
#print axioms N11Formalization.C450SeventhGroupedC06.bound
#print axioms N11Formalization.C450SeventhGroupedC06.endpoint_checks
