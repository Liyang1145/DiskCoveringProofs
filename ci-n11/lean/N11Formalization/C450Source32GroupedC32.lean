import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2479999999:ℚ)/5000000000),((1324735509:ℚ)/2500000000),((9359999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8597438363:ℚ)/10000000000),((-185363441779770279561131412601036123:ℚ)/530450000000000000000000000000000000),((-197055021550245425762040951:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2598749999:ℚ)/5000000000),((27684627:ℚ)/50000000),((3238749999:ℚ)/3560000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((8177266703:ℚ)/10000000000),((-11163901432751215285966398645692677:ℚ)/31684000000000000000000000000000000),((-194548398200661902679540951:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2717499999:ℚ)/5000000000),((1413976093:ℚ)/2500000000),((10072499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((309593599:ℚ)/400000000),((-642112588200576451275451100396724221:ℚ)/1772353500000000000000000000000000000),((-193968297700644522757040951:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((5553749997:ℚ)/10000000000),((2887437727:ℚ)/5000000000),((20501249991:ℚ)/22120000000),(1:ℚ),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1878416793:ℚ)/2500000000),((-47614591847163400416405508184299999:ℚ)/131061000000000000000000000000000000),((-771062702357734296140868559:ℚ)/1478656000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2836249999:ℚ)/5000000000),((1458589541:ℚ)/2500000000),((10428749997:ℚ)/11155000000),(1:ℚ),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((7281879513:ℚ)/10000000000),((-57226275680950724161618310015706579:ℚ)/155542531250000000000000000000000000),((-192511707509647504234540951:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((2865937499:ℚ)/5000000000),((5893839049:ℚ)/10000000000),((1168645833:ℚ)/1250000000),(1:ℚ),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((7163703937:ℚ)/10000000000),((-179845076633762097674454153488327:ℚ)/488281250000000000000000000000000),((-191923061090927475312665951:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2895624999:ℚ)/5000000000),((5953318157:ℚ)/10000000000),((10606874997:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((7043902041:ℚ)/10000000000),((-11864235213840127749889161782973071:ℚ)/32177256250000000000000000000000000),((-191338040154718501538290951:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((2925312499:ℚ)/5000000000),((6012795531:ℚ)/10000000000),((10695937497:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6922386831:ℚ)/10000000000),((-241521457785999876093245995002556293:ℚ)/654368000000000000000000000000000000),((-190756644025706422271415951:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2954999999:ℚ)/5000000000),((3036135607:ℚ)/5000000000),((3594999999:ℚ)/3845000000),(1:ℚ),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((679906387:ℚ)/1000000000),((-128015301634425721011345582599687:ℚ)/346500585937500000000000000000000),((-190178872028577076872040951:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((2984687499:ℚ)/5000000000),((1220401687:ℚ)/2000000000),((10874062497:ℚ)/11582500000),(1:ℚ),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((6673830351:ℚ)/10000000000),((-49849715711256000682036078630920453:ℚ)/134154306250000000000000000000000000),((-190071739571423695420165951:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2999531249:ℚ)/5000000000),((191617039:ℚ)/312500000),((10918593747:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((3305231227:ℚ)/5000000000),((-251405312541257722572305037537110189:ℚ)/676284500000000000000000000000000000),((-189786017603347095814540951:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3014374999:ℚ)/5000000000),((308074083:ℚ)/500000000),((3654374999:ℚ)/3892500000),(1:ℚ),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((102290219:ℚ)/156250000),((-1173934200138669924934750794531299:ℚ)/3156574218750000000000000000000000),((-189501201326657854235790951:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3029218749:ℚ)/5000000000),((3095608837:ℚ)/5000000000),((1572522321:ℚ)/1675000000),(1:ℚ),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((162053733:ℚ)/250000000),((-15657672834010354588675363518915983:ℚ)/42084375000000000000000000000000000),((-189217290694241029243915951:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3044062499:ℚ)/5000000000),((388809581:ℚ)/625000000),((11052187497:ℚ)/11772500000),(1:ℚ),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((6417171887:ℚ)/10000000000),((-257921906666390263840101905452556913:ℚ)/692958781250000000000000000000000000),((-188934285611866737958915951:ℚ)/369664000000000000000000000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3058906249:ℚ)/5000000000),((625068853:ℚ)/1000000000),((3698906249:ℚ)/3940000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3175812213:ℚ)/5000000000),((-14450529179895350312180229036596207:ℚ)/38809000000000000000000000000000000),((-188652186016715058460790951:ℚ)/369664000000000000000000000)⟩
theorem valid14 : Valid source32 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source32 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3073749999:ℚ)/5000000000),((6280423381:ℚ)/10000000000),((11141249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((3142744387:ℚ)/5000000000),((-786914496498188699635630934020271009:ℚ)/2112563343750000000000000000000000000),((-188370991830261088349540951:ℚ)/369664000000000000000000000)⟩
theorem valid15 : Valid source32 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source32 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3088593749:ℚ)/5000000000),((6310157853:ℚ)/10000000000),((11185781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((777343229:ℚ)/1250000000),((-264507814248362467892500623255619039:ℚ)/709836125000000000000000000000000000),((-188090702989684905705165951:ℚ)/369664000000000000000000000)⟩
theorem valid16 : Valid source32 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source32 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3103437499:ℚ)/5000000000),((6369625681:ℚ)/10000000000),((11230312497:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((12302751:ℚ)/20000000),((-133796457641877374605313073223117883:ℚ)/360600250000000000000000000000000000),((-187344351767214017727665951:ℚ)/369664000000000000000000000)⟩
theorem valid17 : Valid source32 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source32 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3133124999:ℚ)/5000000000),((6429092049:ℚ)/10000000000),((1257708333:ℚ)/1345000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1202933357:ℚ)/2000000000),((-1679294309057895211620884309858643:ℚ)/4522562500000000000000000000000000),((-186788311510542296653290951:ℚ)/369664000000000000000000000)⟩
theorem valid18 : Valid source32 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3162812499:ℚ)/5000000000),((648855699:ℚ)/1000000000),((11408437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5875178697:ℚ)/10000000000),((-276528878384908625756735447331030353:ℚ)/744200000000000000000000000000000000),((-186235891239638462726415951:ℚ)/369664000000000000000000000)⟩
theorem valid19 : Valid source32 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source32 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3192499999:ℚ)/5000000000),((3274010269:ℚ)/5000000000),((11497499997:ℚ)/12295000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((1433176391:ℚ)/2500000000),((-70260602076865538837827922832373809:ℚ)/188958781250000000000000000000000000),((-185687090420533179627040951:ℚ)/369664000000000000000000000)⟩
theorem valid20 : Valid source32 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3222187499:ℚ)/5000000000),((3303741363:ℚ)/5000000000),((3862187499:ℚ)/4130000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((2793508097:ℚ)/5000000000),((-31731795445486212467117686934985051:ℚ)/85284500000000000000000000000000000),((-185141908534962091515165951:ℚ)/369664000000000000000000000)⟩
theorem valid21 : Valid source32 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source32 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3251874999:ℚ)/5000000000),((6726403141:ℚ)/10000000000),((11675624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1087569841:ℚ)/2000000000),((-145994733601866765950024250143724079:ℚ)/395641000000000000000000000000000000),((-183666533929741336630790951:ℚ)/369664000000000000000000000)⟩
theorem valid22 : Valid source32 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source32 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3311249999:ℚ)/5000000000),((870528619:ℚ)/1250000000),((1317083333:ℚ)/1440000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2563924721:ℚ)/5000000000),((-1255019556909595594166451598968109:ℚ)/3456000000000000000000000000000000),((-180726813316683882544540951:ℚ)/369664000000000000000000000)⟩
theorem valid23 : Valid source32 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3429999999:ℚ)/5000000000),((7915360891:ℚ)/10000000000),((12209999997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((222475707:ℚ)/500000000),((-1039804513763360777465486557244733239:ℚ)/3145056000000000000000000000000000000),((-172375870527899076142040951:ℚ)/369664000000000000000000000)⟩
theorem valid24 : Valid source32 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3904999999:ℚ)/5000000000),((1108284681:ℚ)/1250000000),((13634999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-429670329883403866895568519583571533:ℚ)/1280000000000000000000000000000000000),((-246309721:ℚ)/512000000)⟩
theorem valid25 : Valid source32 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source32 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4379999999:ℚ)/5000000000),((12668680621:ℚ)/10000000000),((5019999999:ℚ)/7360000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-6611245381093015240002217:ℚ)/27084800000000000000000000),((-246309721:ℚ)/512000000)⟩
theorem valid26 : Valid source32 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet26 valid26
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source32 nn0 nn1 Qcell ((4709:ℚ)/6400) ((4747:ℚ)/6400) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((4747:ℚ)/6400) :=
  cell_join leaf13 node14_16
private theorem node16_18 :
    CellBound source32 nn0 nn1 Qcell ((4747:ℚ)/6400) ((1201:ℚ)/1600) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source32 nn0 nn1 Qcell ((4747:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node16_18 node18_20
private theorem node13_20 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node13_16 node16_20
private theorem node21_23 :
    CellBound source32 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf20 node21_23
private theorem node23_25 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source32 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node23_25 node25_27
private theorem node20_27 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node20_23 node23_27
private theorem node13_27 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node13_20 node20_27
private theorem node0_27 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_27
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_27
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26]
theorem packet_count : packets.length = 27 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC32
#check @N11Formalization.C450Source32GroupedC32.bound
#print axioms N11Formalization.C450Source32GroupedC32.valid0
#print axioms N11Formalization.C450Source32GroupedC32.valid1
#print axioms N11Formalization.C450Source32GroupedC32.valid2
#print axioms N11Formalization.C450Source32GroupedC32.valid3
#print axioms N11Formalization.C450Source32GroupedC32.valid4
#print axioms N11Formalization.C450Source32GroupedC32.valid5
#print axioms N11Formalization.C450Source32GroupedC32.valid6
#print axioms N11Formalization.C450Source32GroupedC32.valid7
#print axioms N11Formalization.C450Source32GroupedC32.valid8
#print axioms N11Formalization.C450Source32GroupedC32.valid9
#print axioms N11Formalization.C450Source32GroupedC32.valid10
#print axioms N11Formalization.C450Source32GroupedC32.valid11
#print axioms N11Formalization.C450Source32GroupedC32.valid12
#print axioms N11Formalization.C450Source32GroupedC32.valid13
#print axioms N11Formalization.C450Source32GroupedC32.valid14
#print axioms N11Formalization.C450Source32GroupedC32.valid15
#print axioms N11Formalization.C450Source32GroupedC32.valid16
#print axioms N11Formalization.C450Source32GroupedC32.valid17
#print axioms N11Formalization.C450Source32GroupedC32.valid18
#print axioms N11Formalization.C450Source32GroupedC32.valid19
#print axioms N11Formalization.C450Source32GroupedC32.valid20
#print axioms N11Formalization.C450Source32GroupedC32.valid21
#print axioms N11Formalization.C450Source32GroupedC32.valid22
#print axioms N11Formalization.C450Source32GroupedC32.valid23
#print axioms N11Formalization.C450Source32GroupedC32.valid24
#print axioms N11Formalization.C450Source32GroupedC32.valid25
#print axioms N11Formalization.C450Source32GroupedC32.valid26
#print axioms N11Formalization.C450Source32GroupedC32.bound
#print axioms N11Formalization.C450Source32GroupedC32.endpoint_checks
