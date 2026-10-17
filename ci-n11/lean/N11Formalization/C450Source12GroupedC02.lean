import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((3273487533:ℚ)/5000000000),((6848178871:ℚ)/10000000000),((-19264536613:ℚ)/19840000000),((-21154412731:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1331724893:ℚ)/2500000000),((916843589094755746372489692807110029888873:ℚ)/20227374016000000000000000000000000000000000),((99066492669444936903840317:ℚ)/277248000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((6784586717:ℚ)/10000000000),((1393392373:ℚ)/2000000000),((-3924177119:ℚ)/4120000000),((-43972107019:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4674754533:ℚ)/10000000000),((4863036125490419498649646264825728738445856173508622617:ℚ)/117425574563183593750000000000000000000000000000000000000),((132429457837925428759825439:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((6903389507:ℚ)/10000000000),((3513176459:ℚ)/5000000000),((-9899529377:ℚ)/10490000000),((-44803726549:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1078742209:ℚ)/2500000000),((80021543986586448521504296161244814550307599408715892754071:ℚ)/2020822716834437890625000000000000000000000000000000000000000),((132599835216581652157794399:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((6962790191:ℚ)/10000000000),((7056048337:ℚ)/10000000000),((-19888145011:ℚ)/21170000000),((-45219531337:ℚ)/53162500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1031030663:ℚ)/2500000000),((648954602915782654748611828597160894371822867593881044977493:ℚ)/16759203823980909863281250000000000000000000000000000000000000),((132685018142478946900634631:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((6992490361:ℚ)/10000000000),((1417148737:ℚ)/2000000000),((-3995446211:ℚ)/4253000000),((-15142477509:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((4025511809:ℚ)/10000000000),((575913389782782803072322929435447814688722587764834793:ℚ)/14876686580471606445312500000000000000000000000000000000),((132770411867456438524244471:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7022190417:ℚ)/10000000000),((1778859741:ℚ)/2500000000),((-5016579223:ℚ)/5340000000),((-45635332919:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((784912551:ℚ)/2000000000),((2018477521637375405443989979513009792302578437345781535269:ℚ)/52153269556696875000000000000000000000000000000000000000000),((398567413453809431857373717:ℚ)/1108992000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((7051890363:ℚ)/10000000000),((3572567087:ℚ)/5000000000),((-10077701261:ℚ)/10727500000),((-45843232541:ℚ)/53875000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3821089699:ℚ)/10000000000),((3466133492949284426216945932214229536269169658693523703867:ℚ)/89579811579706610107421875000000000000000000000000000000000),((398823587981701342415573357:ℚ)/1108992000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7081590199:ℚ)/10000000000),((3579990877:ℚ)/5000000000),((-10099972631:ℚ)/10775000000),((-46051131393:ℚ)/53993750000),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((232180079:ℚ)/625000000),((8562873800121076264532415963336340330516014433723776084851:ℚ)/223743905640850830078125000000000000000000000000000000000000),((132983782993366802102065751:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1774110019:ℚ)/2500000000),((7174829317:ℚ)/10000000000),((-20244487951:ℚ)/21597500000),((-3846256711:ℚ)/4509375000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((457584621:ℚ)/1250000000),((104522989883418467638856645334995797684550668043233153666099:ℚ)/2731378522901238262939453125000000000000000000000000000000000),((8314154864476869165910511:ℚ)/23104000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3555644963:ℚ)/5000000000),((7189676863:ℚ)/10000000000),((-20289030589:ℚ)/21645000000),((-23129514741:ℚ)/27115625000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((3605695253:ℚ)/10000000000),((3804017469038940508412481975773825261662588774593900197218169:ℚ)/99414731823704298193359375000000000000000000000000000000000000),((33267293098413504478730719:ℚ)/92416000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((28504559:ℚ)/40000000),((900565549:ℚ)/1250000000),((-2541696647:ℚ)/2711562500),((-185451913:ℚ)/217400000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((3549899933:ℚ)/10000000000),((704144466610322007566973532965404816644449427654842190363:ℚ)/18403819955844547200202941894531250000000000000000000000000),((2129789866870928431751:ℚ)/5914624000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((7140989547:ℚ)/10000000000),((1443874381:ℚ)/2000000000),((-4075623143:ℚ)/4348000000),((-46466926829:ℚ)/54468750000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((3493251963:ℚ)/10000000000),((1586726742338906439077784146845392304587075583467762547:ℚ)/41474971641407812500000000000000000000000000000000000000),((399463682075575051928721677:ℚ)/1108992000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3577919659:ℚ)/5000000000),((3617109701:ℚ)/5000000000),((-10211329103:ℚ)/10893750000),((-23285437613:ℚ)/27293750000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((3435709101:ℚ)/10000000000),((487321235088293093927209517283664955491914591201943202261:ℚ)/12739043963215517997741699218750000000000000000000000000000),((1752595453038471702066549:ℚ)/4864000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3585344531:ℚ)/5000000000),((3624533441:ℚ)/5000000000),((-10233600323:ℚ)/10917500000),((-23337411717:ℚ)/27353125000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((1688612773:ℚ)/5000000000),((135422855998424169069870377633705446834663889852235136418839:ℚ)/3540387577638957501220703125000000000000000000000000000000000),((33309986973438813903130111:ℚ)/92416000000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7185538781:ℚ)/10000000000),((7263914347:ℚ)/10000000000),((-20511743041:ℚ)/21882500000),((-46778771467:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((1658875739:ℚ)/5000000000),((10038547261861455637553787717199479861126764726493468605141:ℚ)/262462249094715451904296875000000000000000000000000000000000),((133282641086104703475886111:ℚ)/369664000000000000000000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7200388473:ℚ)/10000000000),((1455752359:ℚ)/2000000000),((-4111257077:ℚ)/4386000000),((-46882719311:ℚ)/54943750000),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((3257232583:ℚ)/10000000000),((251708912343003690897917191294714788021136353180621876433:ℚ)/6581600416821534375000000000000000000000000000000000000000),((399976002006667435962635237:ℚ)/1108992000000000000000000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((360761907:ℚ)/500000000),((7293609227:ℚ)/10000000000),((-20600827681:ℚ)/21977500000),((-2349333349:ℚ)/2753125000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((127824377:ℚ)/400000000),((30769260689863268705522128531500306669985394657392504236367:ℚ)/804612409450044297790527343750000000000000000000000000000000),((1000260199837333473673997:ℚ)/2772480000000000000000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7230087781:ℚ)/10000000000),((7308456643:ℚ)/10000000000),((-20645369929:ℚ)/22025000000),((-15696871489:ℚ)/18393750000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((3132816777:ℚ)/10000000000),((153581739036910368162520540935132397030205059444137543965567:ℚ)/4016481775284429931640625000000000000000000000000000000000000),((133410719014379262235124111:ℚ)/369664000000000000000000000)⟩
theorem valid17 : Valid source12 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source12 nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7244937397:ℚ)/10000000000),((1830826011:ℚ)/2500000000),((-5172478033:ℚ)/5518125000),((-47194561779:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3068782777:ℚ)/10000000000),((1740218270897654023751541312384681822286963489676207189:ℚ)/45514136779256916046142578125000000000000000000000000000),((133453411113303455969070959:ℚ)/369664000000000000000000000)⟩
theorem valid18 : Valid source12 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source12 nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1814946747:ℚ)/2500000000),((3676499399:ℚ)/5000000000),((-10389498197:ℚ)/11060000000),((-11824627229:ℚ)/13884375000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1501713979:ℚ)/5000000000),((6396711251404577152590149527730897379615869657461086947637:ℚ)/165591291218346875000000000000000000000000000000000000000000),((1317818149217286430159583:ℚ)/3648000000000000000000000)⟩
theorem valid19 : Valid source12 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3644743047:ℚ)/5000000000),((7382693491:ℚ)/10000000000),((-20868080473:ℚ)/22215000000),((-23753201329:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2868392637:ℚ)/10000000000),((91469682965400501741362769502111230331254674588378912897231:ℚ)/2368403087398740380859375000000000000000000000000000000000000),((100218216401110815601008677:ℚ)/277248000000000000000000000)⟩
theorem valid20 : Valid source12 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3659592551:ℚ)/5000000000),((3706194061:ℚ)/5000000000),((-10478582183:ℚ)/11155000000),((-23857147857:ℚ)/28006250000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((2726871463:ℚ)/10000000000),((18277454700170920544907936068324260392431544047410706566663:ℚ)/473359186991852392578125000000000000000000000000000000000000),((33427417548651422276093751:ℚ)/92416000000000000000000000)⟩
theorem valid21 : Valid source12 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((7348884011:ℚ)/10000000000),((3721041347:ℚ)/5000000000),((-10523124041:ℚ)/11202500000),((-47922188077:ℚ)/56250000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((257779579:ℚ)/1000000000),((1907992573140852631384628009980910080560889735930783:ℚ)/49425082383361816406250000000000000000000000000000000),((7041844777652139638065909:ℚ)/19456000000000000000000000)⟩
theorem valid22 : Valid source12 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((295143313:ℚ)/400000000),((7501471659:ℚ)/10000000000),((-21224414977:ℚ)/22500000000),((-1925203191:ℚ)/2269000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2419769069:ℚ)/10000000000),((100209977511698856750381635626181754707162460003434060360191:ℚ)/2545271246337890625000000000000000000000000000000000000000000),((214345656239386852189319:ℚ)/591462400000000000000000)⟩
theorem valid23 : Valid source12 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((929747521:ℚ)/1250000000),((7560860391:ℚ)/10000000000),((-21402581173:ℚ)/22690000000),((-6068232647:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2068554001:ℚ)/10000000000),((146856061511629871565664664632913690249600892246720146899:ℚ)/3732463664811578125000000000000000000000000000000000000000),((2095887352793579266855091:ℚ)/5776000000000000000000000)⟩
theorem valid24 : Valid source12 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7497377139:ℚ)/10000000000),((1559682623:ℚ)/2000000000),((-4423047869:ℚ)/4576000000),((-48961639973:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((32904111:ℚ)/200000000),((47749380220641929335338406888553519248829483337926706881:ℚ)/1089461274844800000000000000000000000000000000000000000000),((402747501110847073470228413:ℚ)/1108992000000000000000000000)⟩
theorem valid25 : Valid source12 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-15:ℚ)/16),((-7:ℚ)/8),((773496149:ℚ)/1000000000),((1004495319:ℚ)/1250000000),((-2853485957:ℚ)/2955000000),((-5062473043:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((544369894054792322237933003118911984060423192656911097:ℚ)/12501752753759765625000000000000000000000000000000000000),((11621223:ℚ)/32000000)⟩
theorem valid26 : Valid source12 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((996567573:ℚ)/1250000000),((1063881591:ℚ)/1250000000),((-3031644773:ℚ)/3050000000),((-6535973011:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4841769959161021638429705720933579318570717808500733:ℚ)/99338708496093750000000000000000000000000000000000000),((11621223:ℚ)/32000000)⟩
theorem valid27 : Valid source12 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((2111921213:ℚ)/2500000000),((5205663873:ℚ)/5000000000),(-1:ℚ),((-13903448491:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1451382564378573672367139108959243:ℚ)/25000000000000000000000000000000000),((11621223:ℚ)/32000000)⟩
theorem valid28 : Valid source12 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((5174062411:ℚ)/5000000000),((2842330113:ℚ)/2000000000),(-1:ℚ),((-34458436877:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1647904324029095242342499:ℚ)/25392000000000000000000000),((11621223:ℚ)/32000000)⟩
theorem valid29 : Valid source12 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet29 valid29
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_7 node7_15
private theorem node16_18 :
    CellBound source12 nn0 nn1 Qcell ((8791:ℚ)/12800) ((8829:ℚ)/12800) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8829:ℚ)/12800) :=
  cell_join leaf15 node16_18
private theorem node18_20 :
    CellBound source12 nn0 nn1 Qcell ((8829:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound source12 nn0 nn1 Qcell ((8829:ℚ)/12800) ((4481:ℚ)/6400) :=
  cell_join node18_20 node20_22
private theorem node15_22 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_join node15_18 node18_22
private theorem node22_24 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join node22_24 node24_26
private theorem node26_28 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf26 leaf27
private theorem node28_30 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf28 leaf29
private theorem node26_30 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node26_28 node28_30
private theorem node22_30 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node22_26 node26_30
private theorem node15_30 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_22 node22_30
private theorem node0_30 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_30
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_30
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29]
theorem packet_count : packets.length = 30 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC02
#check @N11Formalization.C450Source12GroupedC02.bound
#print axioms N11Formalization.C450Source12GroupedC02.valid0
#print axioms N11Formalization.C450Source12GroupedC02.valid1
#print axioms N11Formalization.C450Source12GroupedC02.valid2
#print axioms N11Formalization.C450Source12GroupedC02.valid3
#print axioms N11Formalization.C450Source12GroupedC02.valid4
#print axioms N11Formalization.C450Source12GroupedC02.valid5
#print axioms N11Formalization.C450Source12GroupedC02.valid6
#print axioms N11Formalization.C450Source12GroupedC02.valid7
#print axioms N11Formalization.C450Source12GroupedC02.valid8
#print axioms N11Formalization.C450Source12GroupedC02.valid9
#print axioms N11Formalization.C450Source12GroupedC02.valid10
#print axioms N11Formalization.C450Source12GroupedC02.valid11
#print axioms N11Formalization.C450Source12GroupedC02.valid12
#print axioms N11Formalization.C450Source12GroupedC02.valid13
#print axioms N11Formalization.C450Source12GroupedC02.valid14
#print axioms N11Formalization.C450Source12GroupedC02.valid15
#print axioms N11Formalization.C450Source12GroupedC02.valid16
#print axioms N11Formalization.C450Source12GroupedC02.valid17
#print axioms N11Formalization.C450Source12GroupedC02.valid18
#print axioms N11Formalization.C450Source12GroupedC02.valid19
#print axioms N11Formalization.C450Source12GroupedC02.valid20
#print axioms N11Formalization.C450Source12GroupedC02.valid21
#print axioms N11Formalization.C450Source12GroupedC02.valid22
#print axioms N11Formalization.C450Source12GroupedC02.valid23
#print axioms N11Formalization.C450Source12GroupedC02.valid24
#print axioms N11Formalization.C450Source12GroupedC02.valid25
#print axioms N11Formalization.C450Source12GroupedC02.valid26
#print axioms N11Formalization.C450Source12GroupedC02.valid27
#print axioms N11Formalization.C450Source12GroupedC02.valid28
#print axioms N11Formalization.C450Source12GroupedC02.valid29
#print axioms N11Formalization.C450Source12GroupedC02.bound
#print axioms N11Formalization.C450Source12GroupedC02.endpoint_checks
