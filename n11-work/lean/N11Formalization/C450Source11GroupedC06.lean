import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((6418627771:ℚ)/10000000000),((1341188653:ℚ)/2000000000),((-13601075183:ℚ)/19840000000),((-5778627771:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5650603519:ℚ)/10000000000),((57441736608423083315754192503452882678705713136443017373629:ℚ)/1553462324428800000000000000000000000000000000000000000000000),((1456282192707445633985129:ℚ)/7393280000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1664090773:ℚ)/2500000000),((3412406071:ℚ)/5000000000),((-34656466781:ℚ)/51500000000),((-1504090773:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1259070961:ℚ)/2500000000),((8299149294731819122084239389298297700768074351526315307781229:ℚ)/234851149126367187500000000000000000000000000000000000000000000),((9099952868222477031242321:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((135504487:ℚ)/200000000),((6943676783:ℚ)/10000000000),((-70620444613:ℚ)/104900000000),((-122704487:ℚ)/213600000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4702017769:ℚ)/10000000000),((4544041021191645706452320445696556729497080095728501470582533:ℚ)/128578694916501562500000000000000000000000000000000000000000000),((36403471876600963616994209:ℚ)/184832000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((6894081643:ℚ)/10000000000),((1400621517:ℚ)/2000000000),((-4751612229:ℚ)/7120000000),((-6254081643:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2172079831:ℚ)/5000000000),((56615952402071138077413260658141834928821476274535204029:ℚ)/1636946830112500000000000000000000000000000000000000000000),((4368008038645403518367227:ℚ)/22179840000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((695350887:ℚ)/1000000000),((706253741:ℚ)/1000000000),((-7192791151:ℚ)/10775000000),((-631350887:ℚ)/1087000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2077242751:ℚ)/5000000000),((319600082389096663207114101077516159291057381439931993200519:ℚ)/9238276192663964843750000000000000000000000000000000000000000),((364020516782023860803561:ℚ)/1848320000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3506467591:ℚ)/5000000000),((1418450393:ℚ)/2000000000),((-14450954323:ℚ)/21740000000),((-3186467591:ℚ)/5458750000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((61816913:ℚ)/156250000),((2620244559060651124431718335180137546923470385204651607133443:ℚ)/76542922093879896875000000000000000000000000000000000000000000),((1456016136308088434368369:ℚ)/7393280000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3521324001:ℚ)/5000000000),((1780491571:ℚ)/2500000000),((-18145407281:ℚ)/27293750000),((-3201324001:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3853572349:ℚ)/10000000000),((5231198421393614694851833592364707284679690022055281350593129:ℚ)/152787180700372271347045898437500000000000000000000000000000000),((2275089648084241401413321:ℚ)/11552000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7072360603:ℚ)/10000000000),((1787920093:ℚ)/2500000000),((-18227121023:ℚ)/27412500000),((-6432360603:ℚ)/11012500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((468524223:ℚ)/1250000000),((855474961092303432788188498635894819114279484531570052239943:ℚ)/24981457727673880004882812500000000000000000000000000000000000),((2275155048066668697128569:ℚ)/11552000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((1775518247:ℚ)/2500000000),((897674279:ℚ)/1250000000),((-9154417069:ℚ)/13765625000),((-230788321:ℚ)/395000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((909978621:ℚ)/2500000000),((81676264452475834915146141343261820596843272683101919279:ℚ)/2384697455362044274806976318359375000000000000000000000000),((568805353228225504129121:ℚ)/2888000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3565892579:ℚ)/5000000000),((1442221573:ℚ)/2000000000),((-14712437303:ℚ)/22120000000),((-1081964193:ℚ)/1851250000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3528466911:ℚ)/10000000000),((3811888929119188052382489196678455167338279802780505313018181:ℚ)/111277347698729100000000000000000000000000000000000000000000000),((1456184795265919698058649:ℚ)/7393280000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7161497117:ℚ)/10000000000),((1810205319:ℚ)/2500000000),((-6157419503:ℚ)/9256250000),((-6521497117:ℚ)/11155000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3413540233:ℚ)/10000000000),((52828301403887476608595811436962139871533929141786130759223:ℚ)/1541929093358554935455322265625000000000000000000000000000000),((6826071111396030921233923:ℚ)/34656000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7191208867:ℚ)/10000000000),((7270534467:ℚ)/10000000000),((-74215879137:ℚ)/111550000000),((-6551208867:ℚ)/11202500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3294769867:ℚ)/10000000000),((238763288318264362524123951706968328591843812515326512132297497:ℚ)/6967847232520067218750000000000000000000000000000000000000000000),((109220462231183499245017627:ℚ)/554496000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((1805230103:ℚ)/2500000000),((91253093:ℚ)/125000000),((-931784023:ℚ)/1400312500),((-1645230103:ℚ)/2812500000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3171723481:ℚ)/10000000000),((744377996834358698339547082279200092096305638212123:ℚ)/21720006906750798225402832031250000000000000000000000),((5688741301570115894069:ℚ)/28880000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7250631753:ℚ)/10000000000),((7329960199:ℚ)/10000000000),((-74869562189:ℚ)/112500000000),((-6610631753:ℚ)/11297500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3043881989:ℚ)/10000000000),((2076333939557490228132393346395080696349357751160280869630251007:ℚ)/60576058630371093750000000000000000000000000000000000000000000000),((36409083353158226950229681:ℚ)/184832000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7280342893:ℚ)/10000000000),((7359672747:ℚ)/10000000000),((-75196400217:ℚ)/112975000000),((-6640342893:ℚ)/11345000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((2910613019:ℚ)/10000000000),((3976425945139936916805157293333229592285477651679197405267537:ℚ)/115994144936326073974609375000000000000000000000000000000000000),((109230713438519654346054187:ℚ)/554496000000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((1827513459:ℚ)/2500000000),((57961697:ℚ)/78125000),((-592578667:ℚ)/886328125),((-1667513459:ℚ)/2860000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2771132997:ℚ)/10000000000),((394526879176736547967197486358528529889879292949851437311:ℚ)/11390575148961114883422851562500000000000000000000000000000),((35561774031339054167339:ℚ)/180500000000000000000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((115148049:ℚ)/156250000),((747852087:ℚ)/1000000000),((-7650372957:ℚ)/11440000000),((-105148049:ℚ)/180234375),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((617320947:ℚ)/2500000000),((22463903874198634087279742442106465584129780821105940791:ℚ)/648473240897625000000000000000000000000000000000000000000),((1092530206334999078497267:ℚ)/5544960000000000000000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((928611959:ℚ)/1250000000),((471121483:ℚ)/625000000),((-4822336313:ℚ)/7209375000),((-848611959:ℚ)/1453750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2125968781:ℚ)/10000000000),((36581395753737293885677122985210327333910410826060528881099:ℚ)/1055871434575403022766113281250000000000000000000000000000000),((142266219622786844375409:ℚ)/722000000000000000000000)⟩
theorem valid17 : Valid source11 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((936039433:ℚ)/1250000000),((3828393567:ℚ)/5000000000),((-39232329237:ℚ)/58150000000),((-856039433:ℚ)/1477500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((343295413:ℚ)/2000000000),((421179941955052260425961838215190143738781771549450074823837:ℚ)/11923441781899023437500000000000000000000000000000000000000000),((11981264090927207:ℚ)/60800000000000000)⟩
theorem valid18 : Valid source11 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((1521430577:ℚ)/2000000000),((7894465207:ℚ)/10000000000),((-81079117277:ℚ)/118200000000),((-1393430577:ℚ)/2440000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((4219389160424854752777418141884343603808831491354862650958639:ℚ)/115216153378650000000000000000000000000000000000000000000000000),((1260839:ℚ)/6400000)⟩
theorem valid19 : Valid source11 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7844819549:ℚ)/10000000000),((4184894997:ℚ)/5000000000),((-43153844967:ℚ)/61000000000),((-7204819549:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((363125958829622821302453963544614702828932077432465991062783:ℚ)/9307639631250000000000000000000000000000000000000000000000000),((1260839:ℚ)/6400000)⟩
theorem valid20 : Valid source11 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((832012353:ℚ)/1000000000),((5135390181:ℚ)/5000000000),((-661843111:ℚ)/800000000),((-768012353:ℚ)/1600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((498805226275300854850296891225340970643474924866773:ℚ)/9600000000000000000000000000000000000000000000000000),((1260839:ℚ)/6400000)⟩
theorem valid21 : Valid source11 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((2555262617:ℚ)/2500000000),((14071942599:ℚ)/10000000000),((-149031368589:ℚ)/160000000000),((-2395262617:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((317804053728566968924738628225912768279807:ℚ)/4875264000000000000000000000000000000000000),((1260839:ℚ)/6400000)⟩
theorem valid22 : Valid source11 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source11 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((881:ℚ)/1280) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC06
#check @N11Formalization.C450Source11GroupedC06.bound
#print axioms N11Formalization.C450Source11GroupedC06.valid0
#print axioms N11Formalization.C450Source11GroupedC06.valid1
#print axioms N11Formalization.C450Source11GroupedC06.valid2
#print axioms N11Formalization.C450Source11GroupedC06.valid3
#print axioms N11Formalization.C450Source11GroupedC06.valid4
#print axioms N11Formalization.C450Source11GroupedC06.valid5
#print axioms N11Formalization.C450Source11GroupedC06.valid6
#print axioms N11Formalization.C450Source11GroupedC06.valid7
#print axioms N11Formalization.C450Source11GroupedC06.valid8
#print axioms N11Formalization.C450Source11GroupedC06.valid9
#print axioms N11Formalization.C450Source11GroupedC06.valid10
#print axioms N11Formalization.C450Source11GroupedC06.valid11
#print axioms N11Formalization.C450Source11GroupedC06.valid12
#print axioms N11Formalization.C450Source11GroupedC06.valid13
#print axioms N11Formalization.C450Source11GroupedC06.valid14
#print axioms N11Formalization.C450Source11GroupedC06.valid15
#print axioms N11Formalization.C450Source11GroupedC06.valid16
#print axioms N11Formalization.C450Source11GroupedC06.valid17
#print axioms N11Formalization.C450Source11GroupedC06.valid18
#print axioms N11Formalization.C450Source11GroupedC06.valid19
#print axioms N11Formalization.C450Source11GroupedC06.valid20
#print axioms N11Formalization.C450Source11GroupedC06.valid21
#print axioms N11Formalization.C450Source11GroupedC06.valid22
#print axioms N11Formalization.C450Source11GroupedC06.bound
#print axioms N11Formalization.C450Source11GroupedC06.endpoint_checks
