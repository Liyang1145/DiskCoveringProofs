import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/8),((15:ℚ)/16),((330687091:ℚ)/625000000),((702134219:ℚ)/1250000000),((2774809637:ℚ)/3218750000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((4003646549:ℚ)/5000000000),((-128838893704779606768223448668154247:ℚ)/333473815917968750000000000000000000),((-480948958137191263833559:ℚ)/1444000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5528826193:ℚ)/10000000000),((46840991:ℚ)/80000000),((46061783351:ℚ)/53400000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7561585251:ℚ)/10000000000),((-53156534450228906186271691176667001387225594626627583:ℚ)/137689257812500000000000000000000000000000000000000000),((-119745830050230159095895111:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((2883317603:ℚ)/5000000000),((1194826893:ℚ)/2000000000),((23863223221:ℚ)/27175000000),((1399626893:ℚ)/1424000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3546885239:ℚ)/5000000000),((-50765134223511059081658710934845769518899165297317275351:ℚ)/125426318652343750000000000000000000000000000000000000000),((-29524275548380761323173151:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1177106319:ℚ)/2000000000),((6093136073:ℚ)/10000000000),((9711744233:ℚ)/11060000000),((21351408219:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3425055283:ℚ)/5000000000),((-53403048474535616068153882325413178613775507251717923:ℚ)/132119044531250000000000000000000000000000000000000000),((-13969402268850362594914837:ℚ)/44359680000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3002211473:ℚ)/5000000000),((6152633653:ℚ)/10000000000),((24695480311:ℚ)/27887500000),((3075700137:ℚ)/3160000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3299482779:ℚ)/5000000000),((-3500312166668223310010404294651465627487840094516034789:ℚ)/8472055352020263671875000000000000000000000000000000000),((-28897357474016742972365831:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((1515966703:ℚ)/2500000000),((1553032289:ℚ)/2500000000),((12451766921:ℚ)/14062500000),((5427096867:ℚ)/5577500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((101098561:ℚ)/156250000),((-28027255121702631691805956953745525507115782053958931:ℚ)/67893415689468383789062500000000000000000000000000000),((-7171718571942042264492551:ℚ)/23104000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3061654757:ℚ)/5000000000),((1567905659:ℚ)/2500000000),((25111583299:ℚ)/28362500000),((607968553:ℚ)/625000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6339423503:ℚ)/10000000000),((-147046092886161365068018131649182733394265339021979481:ℚ)/356495089996337890625000000000000000000000000000000000),((-28476448340301460329551311:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((154568777:ℚ)/250000000),((6331114141:ℚ)/10000000000),((1265981439:ℚ)/1430000000),((22065342423:ℚ)/22690000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3103084349:ℚ)/5000000000),((-7532634471086411598059105182300015253099481846725429:ℚ)/18276293750000000000000000000000000000000000000000000),((-70665198643047258972331:ℚ)/231040000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3121095769:ℚ)/5000000000),((3195301861:ℚ)/5000000000),((8509223461:ℚ)/9612500000),((11121905583:ℚ)/11440000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((758798073:ℚ)/1250000000),((-89305497740120487638560375337664149291573940142519:ℚ)/216844849109649658203125000000000000000000000000000),((-28055767453347685033490679:ℚ)/92416000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((1575407729:ℚ)/2500000000),((3210173903:ℚ)/5000000000),((12867854103:ℚ)/14478125000),((3722173903:ℚ)/3845000000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((1186378927:ℚ)/2000000000),((-315703315170322103519886367355539306036685535545710237:ℚ)/758712037178039550781250000000000000000000000000000000),((-6988319260673446823725799:ℚ)/23104000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6331350209:ℚ)/10000000000),((3225045713:ℚ)/5000000000),((51679451463:ℚ)/58150000000),((99213603:ℚ)/102500000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((2930787147:ℚ)/5000000000),((-511152939746257197834423703534481518554037256476703251933:ℚ)/1228935739843750000000000000000000000000000000000000000000),((-111392675804389662897453159:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6361069241:ℚ)/10000000000),((1619958647:ℚ)/2500000000),((17295828229:ℚ)/19462500000),((5627875941:ℚ)/5815000000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((1158100367:ℚ)/2000000000),((-1558974080935240563373315965212538690616036713499637:ℚ)/3749684187769889831542968750000000000000000000000000),((-110972299982771677564216759:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((6390788017:ℚ)/10000000000),((3254788649:ℚ)/5000000000),((52095516119:ℚ)/58625000000),((3766788649:ℚ)/3892500000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((5718648851:ℚ)/10000000000),((-523357267501878128636235959206048144707297614008649235101:ℚ)/1259298205566406250000000000000000000000000000000000000000),((-110551980619457777169601671:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((3210253269:ℚ)/5000000000),((3269659781:ℚ)/5000000000),((26151772883:ℚ)/29431250000),((11344979343:ℚ)/11725000000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((1411496297:ℚ)/2500000000),((-3893635413612397564677057985644316741328465579801947681:ℚ)/9372538203430175781250000000000000000000000000000000000),((-82598788219923233720217037:ℚ)/277248000000000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6450224809:ℚ)/10000000000),((6569061383:ℚ)/10000000000),((52511573663:ℚ)/59100000000),((22779184149:ℚ)/23545000000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2786239383:ℚ)/5000000000),((-44646821665228748016351178031448396277825380354087118079:ℚ)/107513057812500000000000000000000000000000000000000000000),((-109711510961152507508902359:ℚ)/369664000000000000000000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6479942833:ℚ)/10000000000),((6598802769:ℚ)/10000000000),((52719599831:ℚ)/59337500000),((7622802769:ℚ)/7880000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((1099619083:ℚ)/2000000000),((-542039827659560483653995981190701491336018171308263987221:ℚ)/1305773202185058593750000000000000000000000000000000000000),((-109291360507121052457032071:ℚ)/369664000000000000000000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6509660611:ℚ)/10000000000),((1657135931:ℚ)/2500000000),((52927624277:ℚ)/59575000000),((5739407793:ℚ)/5933750000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((2711399343:ℚ)/5000000000),((-548368548223658963424683233576612834536491800588072730087:ℚ)/1321515223339843750000000000000000000000000000000000000000),((-108871266205621808828713119:ℚ)/369664000000000000000000000)⟩
theorem valid16 : Valid source25 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source25 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1634844537:ℚ)/2500000000),((6688024363:ℚ)/10000000000),((13283911759:ℚ)/15012500000),((23136073089:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5346549611:ℚ)/10000000000),((-2169812722789312251520330538957621275581401524953701029:ℚ)/5286632083129882812500000000000000000000000000000000000),((-20253791121585641621832373:ℚ)/69312000000000000000000000)⟩
theorem valid17 : Valid source25 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source25 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1649703127:ℚ)/2500000000),((6747503339:ℚ)/10000000000),((13387921889:ℚ)/15131250000),((23314510017:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2595512263:ℚ)/5000000000),((-2220348061687433166770889195683903001730226315766565619:ℚ)/5413080009841918945312500000000000000000000000000000000),((-6698770172874418506743431:ℚ)/23104000000000000000000000)⟩
theorem valid18 : Valid source25 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((3329122967:ℚ)/5000000000),((6806980691:ℚ)/10000000000),((26983860769:ℚ)/30500000000),((2610326897:ℚ)/2690000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5031148027:ℚ)/10000000000),((-72694110745798054403768110002181843156990101420408242179:ℚ)/177328906250000000000000000000000000000000000000000000000),((-26585162344236677425422871:ℚ)/92416000000000000000000000)⟩
theorem valid19 : Valid source25 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source25 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((134353569:ℚ)/200000000),((277037227:ℚ)/400000000),((1087674983:ℚ)/1239000000),((953991681:ℚ)/976000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((194659523:ℚ)/400000000),((-530212277456352797097536194739698881771042954376997:ℚ)/1320843693750000000000000000000000000000000000000000),((-125567121889955519350837:ℚ)/443596800000000000000000)⟩
theorem valid20 : Valid source25 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6836540831:ℚ)/10000000000),((7044874603:ℚ)/10000000000),((3247987401:ℚ)/3700000000),((8068874603:ℚ)/8260000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((904139767:ℚ)/2000000000),((-31748444563461827983275155384716375589358619087860219:ℚ)/79145312500000000000000000000000000000000000000000000),((-102961075748408258104509479:ℚ)/369664000000000000000000000)⟩
theorem valid21 : Valid source25 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((1738849953:ℚ)/2500000000),((3641372681:ℚ)/5000000000),((14011949671:ℚ)/16200000000),((12460118043:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((518539559:ℚ)/1250000000),((-126484177144203513917298158220072007087584196500604141:ℚ)/328050000000000000000000000000000000000000000000000000),((-18667525150544432512781653:ℚ)/69312000000000000000000000)⟩
theorem valid22 : Valid source25 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((7193108177:ℚ)/10000000000),((8234033413:ℚ)/10000000000),((57711757239:ℚ)/72400000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((205439819:ℚ)/625000000),((-45910715565422035394221142596594691984645170231635126349:ℚ)/148243525000000000000000000000000000000000000000000000000),((-95057518103692214123036231:ℚ)/369664000000000000000000000)⟩
theorem valid23 : Valid source25 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((162876643:ℚ)/200000000),((9185076329:ℚ)/10000000000),((1287336501:ℚ)/1600000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-2034316129519592007868591212112466614804025661512631:ℚ)/6400000000000000000000000000000000000000000000000000),((-2060853:ℚ)/8000000)⟩
theorem valid24 : Valid source25 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source25 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((227360461:ℚ)/250000000),((1298781063:ℚ)/1000000000),((1775523227:ℚ)/2760000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-89666948225631693577567850314291:ℚ)/584016000000000000000000000000000),((-2060853:ℚ)/8000000)⟩
theorem valid25 : Valid source25 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet25 valid25
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source25 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source25 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source25 nn0 nn1 Qcell ((4709:ℚ)/6400) ((4747:ℚ)/6400) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((4747:ℚ)/6400) :=
  cell_join leaf13 node14_16
private theorem node17_19 :
    CellBound source25 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source25 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_join leaf16 node17_19
private theorem node13_19 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((2421:ℚ)/3200) :=
  cell_join node13_16 node16_19
private theorem node20_22 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source25 nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf19 node20_22
private theorem node22_24 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source25 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node22_24 node24_26
private theorem node19_26 :
    CellBound source25 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node19_22 node22_26
private theorem node13_26 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node13_19 node19_26
private theorem node0_26 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_26
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_26
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25]
theorem packet_count : packets.length = 26 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC31
#check @N11Formalization.C450Source25GroupedC31.bound
#print axioms N11Formalization.C450Source25GroupedC31.valid0
#print axioms N11Formalization.C450Source25GroupedC31.valid1
#print axioms N11Formalization.C450Source25GroupedC31.valid2
#print axioms N11Formalization.C450Source25GroupedC31.valid3
#print axioms N11Formalization.C450Source25GroupedC31.valid4
#print axioms N11Formalization.C450Source25GroupedC31.valid5
#print axioms N11Formalization.C450Source25GroupedC31.valid6
#print axioms N11Formalization.C450Source25GroupedC31.valid7
#print axioms N11Formalization.C450Source25GroupedC31.valid8
#print axioms N11Formalization.C450Source25GroupedC31.valid9
#print axioms N11Formalization.C450Source25GroupedC31.valid10
#print axioms N11Formalization.C450Source25GroupedC31.valid11
#print axioms N11Formalization.C450Source25GroupedC31.valid12
#print axioms N11Formalization.C450Source25GroupedC31.valid13
#print axioms N11Formalization.C450Source25GroupedC31.valid14
#print axioms N11Formalization.C450Source25GroupedC31.valid15
#print axioms N11Formalization.C450Source25GroupedC31.valid16
#print axioms N11Formalization.C450Source25GroupedC31.valid17
#print axioms N11Formalization.C450Source25GroupedC31.valid18
#print axioms N11Formalization.C450Source25GroupedC31.valid19
#print axioms N11Formalization.C450Source25GroupedC31.valid20
#print axioms N11Formalization.C450Source25GroupedC31.valid21
#print axioms N11Formalization.C450Source25GroupedC31.valid22
#print axioms N11Formalization.C450Source25GroupedC31.valid23
#print axioms N11Formalization.C450Source25GroupedC31.valid24
#print axioms N11Formalization.C450Source25GroupedC31.valid25
#print axioms N11Formalization.C450Source25GroupedC31.bound
#print axioms N11Formalization.C450Source25GroupedC31.endpoint_checks
