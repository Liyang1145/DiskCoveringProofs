import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((6348588547:ℚ)/10000000000),((1326195887:ℚ)/2000000000),((-535501501:ℚ)/640000000),((-18085765641:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5684026:ℚ)/9765625),((332729309722353753218428315985184876627469005922730167:ℚ)/26072678400000000000000000000000000000000000000000000000),((174440541558400155590171:ℚ)/1155200000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((6586140631:ℚ)/10000000000),((6868533549:ℚ)/10000000000),((-86090936137:ℚ)/103000000000),((-6266140631:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1306133861:ℚ)/2500000000),((85912557921995630258468583319007511804759053595754196457313:ℚ)/6762102005468750000000000000000000000000000000000000000000000),((4369929377810858496806859:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6823689007:ℚ)/10000000000),((6987309187:ℚ)/10000000000),((-87635019431:ℚ)/106800000000),((-19511067021:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((36474059:ℚ)/80000000),((17837346034313138252716017490884540635353340336809111301304493:ℚ)/1499345129449800000000000000000000000000000000000000000000000000),((4374419367358496438697971:ℚ)/28880000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((6942461927:ℚ)/10000000000),((7046696673:ℚ)/10000000000),((-88407056749:ℚ)/108700000000),((-6622461927:ℚ)/9137500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((523794277:ℚ)/1250000000),((6174288557269066254194084812925999551220398425293867917976909:ℚ)/536183464491080468750000000000000000000000000000000000000000000),((4376672380265121717304611:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((7001848089:ℚ)/10000000000),((1415278067:ℚ)/2000000000),((-17758614871:ℚ)/21930000000),((-20045544267:ℚ)/27531250000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3993966007:ℚ)/10000000000),((72455577235181872155759036581971281613080911177679406516519:ℚ)/6395253178284513281250000000000000000000000000000000000000000),((175112035652437223987651:ℚ)/1155200000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7031541097:ℚ)/10000000000),((888260493:ℚ)/1250000000),((-11147386409:ℚ)/13765625000),((-20134623291:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3892267189:ℚ)/10000000000),((378294414690365324958903269632107859380907870803929939347:ℚ)/33385764375068619847297668457031250000000000000000000000000),((136841585586877297037757:ℚ)/902500000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7061234059:ℚ)/10000000000),((7135777501:ℚ)/10000000000),((-12795015359:ℚ)/15800000000),((-6741234059:ℚ)/9256250000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1893990899:ℚ)/5000000000),((229780900666862661783613892655527757761072990703131328238037:ℚ)/20276484638981250000000000000000000000000000000000000000000000),((4380061922703501327433259:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7090926973:ℚ)/10000000000),((3582735503:ℚ)/5000000000),((-44975561539:ℚ)/55537500000),((-20312780919:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((460111191:ℚ)/1250000000),((1887383873002880323670852720648722315651059500943836140868731:ℚ)/166528342082723933029174804687500000000000000000000000000000000),((1095298610768545598630081:ℚ)/7220000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3560309921:ℚ)/5000000000),((7195164461:ℚ)/10000000000),((-90337137993:ℚ)/111550000000),((-10200929763:ℚ)/14003125000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((1785368669:ℚ)/5000000000),((39490233889911512518314917985253151344363452357249742639846393:ℚ)/3483923616260033609375000000000000000000000000000000000000000000),((4382328299961500950612939:ℚ)/28880000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((1430062533:ℚ)/2000000000),((1444971573:ℚ)/2000000000),((-18144630449:ℚ)/22405000000),((-1366062533:ℚ)/1875000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((432154033:ℚ)/1250000000),((4669113635167423672510731722226506787750626044410907:ℚ)/411875686528015136718750000000000000000000000000000000),((175338539732817710783211:ℚ)/1155200000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7180005443:ℚ)/10000000000),((7254551219:ℚ)/10000000000),((-30369721949:ℚ)/37500000000),((-20580016329:ℚ)/28243750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1670015989:ℚ)/5000000000),((12718063180343314970174976086582022808867184286550137620575847:ℚ)/1121778863525390625000000000000000000000000000000000000000000000),((4384600023182409540506899:ℚ)/28880000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7209698177:ℚ)/10000000000),((1821061131:ℚ)/2500000000),((-22873794703:ℚ)/28243750000),((-20669094531:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3218732319:ℚ)/10000000000),((10275039850652620759289433708967716982463736336964056578623:ℚ)/906204257315047452926635742187500000000000000000000000000000),((34263577262335806734853:ℚ)/225625000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3619695433:ℚ)/5000000000),((7313937781:ℚ)/10000000000),((-91881191153:ℚ)/113450000000),((-3459695433:ℚ)/4746875000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((61857009:ℚ)/200000000),((119392887427712072170768162839154753709675004361465905757755313:ℚ)/10528804702067714453125000000000000000000000000000000000000000000),((4386877092541926241743899:ℚ)/28880000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((7269083513:ℚ)/10000000000),((734363099:ℚ)/1000000000),((-3075573429:ℚ)/3797500000),((-20847250539:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((740450397:ℚ)/2500000000),((116385993540674490187933738091017959314035248569099521:ℚ)/10262686564990234375000000000000000000000000000000000000),((43880176320647477711209:ℚ)/288800000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((7298776117:ℚ)/10000000000),((921665519:ℚ)/1250000000),((-11581651747:ℚ)/14300000000),((-20936328351:ℚ)/28718750000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((1412433061:ℚ)/5000000000),((262596330989982016449175916888271517797316809533094564984721:ℚ)/23153167388690625000000000000000000000000000000000000000000000),((137161234630607360953123:ℚ)/902500000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3664234339:ℚ)/5000000000),((7403017267:ℚ)/10000000000),((-93039224471:ℚ)/114875000000),((-3504234339:ℚ)/4806250000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1340570813:ℚ)/5000000000),((3723709031388861570732453973177081393857917538687711657557:ℚ)/328292199670171022415161132812500000000000000000000000000000),((4390302720879634114872851:ℚ)/28880000000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3679080599:ℚ)/5000000000),((46640021:ℚ)/62500000),((-195440091:ℚ)/240312500),((-10557241797:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1264735219:ℚ)/5000000000),((675635641753562484155762868580489593876752896801068871:ℚ)/58659524143077945709228515625000000000000000000000000000),((1372685361301748834627:ℚ)/9025000000000000000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((3708773057:ℚ)/5000000000),((7581175011:ℚ)/10000000000),((-95355275143:ℚ)/116300000000),((-3548773057:ℚ)/4925000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((439124281:ℚ)/2000000000),((565674780389763399541401104299578781879850771163948726263103:ℚ)/47693767127596093750000000000000000000000000000000000000000000),((4397190066611197761804339:ℚ)/28880000000000000000000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-13:ℚ)/16),((-3:ℚ)/4),((7536315469:ℚ)/10000000000),((61083721:ℚ)/78125000),((-256362791:ℚ)/307812500),((-21648946407:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1295474631:ℚ)/10000000000),((101878197455913311833150841232721498973908241594749069:ℚ)/8139161949062347412109375000000000000000000000000000000),((19492169:ℚ)/128000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((777385237:ℚ)/1000000000),((8293791579:ℚ)/10000000000),((-104619290527:ℚ)/122000000000),((-745385237:ℚ)/1080000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((56826464046577630657021163314584297103615868281981707698567:ℚ)/4136728725000000000000000000000000000000000000000000000000000),((19492169:ℚ)/128000000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8248919679:ℚ)/10000000000),((2038804241:ℚ)/2000000000),((-25864455133:ℚ)/25920000000),((-23786759037:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((210451080929669091806260186447538133920059014625484791:ℚ)/10203667200000000000000000000000000000000000000000000000),((19492169:ℚ)/128000000)⟩
theorem valid20 : Valid seventh packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10149124959:ℚ)/10000000000),((2798858149:ℚ)/2000000000),(-1:ℚ),((-9829124959:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((383543024219351645715247:ℚ)/16928000000000000000000000),((19492169:ℚ)/128000000)⟩
theorem valid21 : Valid seventh packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((881:ℚ)/1280) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((881:ℚ)/1280) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((881:ℚ)/1280) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound seventh nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound seventh nn0 nn1 Qcell ((881:ℚ)/1280) ((4519:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC04
#check @N11Formalization.C450SeventhGroupedC04.bound
#print axioms N11Formalization.C450SeventhGroupedC04.valid0
#print axioms N11Formalization.C450SeventhGroupedC04.valid1
#print axioms N11Formalization.C450SeventhGroupedC04.valid2
#print axioms N11Formalization.C450SeventhGroupedC04.valid3
#print axioms N11Formalization.C450SeventhGroupedC04.valid4
#print axioms N11Formalization.C450SeventhGroupedC04.valid5
#print axioms N11Formalization.C450SeventhGroupedC04.valid6
#print axioms N11Formalization.C450SeventhGroupedC04.valid7
#print axioms N11Formalization.C450SeventhGroupedC04.valid8
#print axioms N11Formalization.C450SeventhGroupedC04.valid9
#print axioms N11Formalization.C450SeventhGroupedC04.valid10
#print axioms N11Formalization.C450SeventhGroupedC04.valid11
#print axioms N11Formalization.C450SeventhGroupedC04.valid12
#print axioms N11Formalization.C450SeventhGroupedC04.valid13
#print axioms N11Formalization.C450SeventhGroupedC04.valid14
#print axioms N11Formalization.C450SeventhGroupedC04.valid15
#print axioms N11Formalization.C450SeventhGroupedC04.valid16
#print axioms N11Formalization.C450SeventhGroupedC04.valid17
#print axioms N11Formalization.C450SeventhGroupedC04.valid18
#print axioms N11Formalization.C450SeventhGroupedC04.valid19
#print axioms N11Formalization.C450SeventhGroupedC04.valid20
#print axioms N11Formalization.C450SeventhGroupedC04.valid21
#print axioms N11Formalization.C450SeventhGroupedC04.bound
#print axioms N11Formalization.C450SeventhGroupedC04.endpoint_checks
