import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((3188983703:ℚ)/5000000000),((1665732563:ℚ)/2500000000),((-20694523319:ℚ)/24800000000),((-9006951109:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2874871879:ℚ)/5000000000),((53641562647003441034826850911052718678290256946042924372091:ℚ)/3034106102400000000000000000000000000000000000000000000000000),((2563071814589902935950583:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3307771209:ℚ)/5000000000),((847714719:ℚ)/1250000000),((-10540291347:ℚ)/12875000000),((-9363313627:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2573239321:ℚ)/5000000000),((60764583830928730956882388810612519039490564317439308172189:ℚ)/3669549205099487304687500000000000000000000000000000000000000),((641480730765789864550927:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((1346865577:ℚ)/2000000000),((3450251959:ℚ)/5000000000),((-42933275467:ℚ)/52450000000),((-3816596731:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1204858783:ℚ)/2500000000),((265982194621476039358597033533190874653070130443359620044629:ℚ)/16072336864562695312500000000000000000000000000000000000000000),((10275139789178749201985967:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((685311209:ℚ)/1000000000),((3479948261:ℚ)/5000000000),((-43319327393:ℚ)/53400000000),((-1943933627:ℚ)/2693750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((558815553:ℚ)/1250000000),((33219893880106649353603715775521832074826016979271983121757:ℚ)/2071760831861132812500000000000000000000000000000000000000000),((10280880212873981663019047:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((345625187:ℚ)/500000000),((3509644409:ℚ)/5000000000),((-43705377317:ℚ)/53875000000),((-980875561:ℚ)/1358750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1071551203:ℚ)/2500000000),((18517514057386769573450057902567854575539684215839742975336059:ℚ)/1154784524082995605468750000000000000000000000000000000000000000),((10286631554253745297257167:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3485947549:ℚ)/5000000000),((3539340407:ℚ)/5000000000),((-44091425291:ℚ)/54350000000),((-9897842647:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1023532691:ℚ)/2500000000),((19346218172811956588130663559044803924199137480155934384651653:ℚ)/1206412795104931054687500000000000000000000000000000000000000000),((10292393813924628524503343:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((3515643087:ℚ)/5000000000),((3554188351:ℚ)/5000000000),((-44284448563:ℚ)/54825000000),((-9986929261:ℚ)/13765625000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((486643877:ℚ)/1250000000),((3155913827083400097043824261328677976273421259286798607105261:ℚ)/199851661821391040039062500000000000000000000000000000000000000),((10295279038310411928740607:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7060981607:ℚ)/10000000000),((7138072519:ℚ)/10000000000),((-88954942747:ℚ)/110125000000),((-20062944821:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3788879939:ℚ)/10000000000),((269955792300856046157011241263660903332173210338834945780129:ℚ)/17093511360035133361816406250000000000000000000000000000000000),((41192667970385665004275727:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1772669243:ℚ)/2500000000),((895971033:ℚ)/1250000000),((-11167623429:ℚ)/13825000000),((-5038007729:ℚ)/6942187500),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((368180359:ℚ)/1000000000),((429092120663654183371003487334063130749754314978168140620249:ℚ)/27167321215510034179687500000000000000000000000000000000000000),((643816104791601359311423:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((712037227:ℚ)/1000000000),((3598731969:ℚ)/5000000000),((-14954505199:ℚ)/18512500000),((-2024111681:ℚ)/2788750000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((55807331:ℚ)/156250000),((194849301847594178826731835984540597801090894931598846765097:ℚ)/12335432746868439483642578125000000000000000000000000000000000),((10303951090595603318476927:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3575033751:ℚ)/5000000000),((903394943:ℚ)/1250000000),((-11264134259:ℚ)/13943750000),((-10165101253:ℚ)/14003125000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((691636811:ℚ)/2000000000),((214987036452593522645617953060220731565658572279553012881837:ℚ)/13609076626015756286621093750000000000000000000000000000000000),((644177952166215756206543:ℚ)/3610000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((1794940667:ℚ)/2500000000),((181421377:ℚ)/250000000),((-2262477901:ℚ)/2800625000),((-5104822001:ℚ)/7031250000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3341006259:ℚ)/10000000000),((228765163946817867192926261652952846964960516700089:ℚ)/14480004604500532150268554687500000000000000000000000),((25774365271607588782703:ℚ)/144400000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7209457769:ℚ)/10000000000),((145731011:ℚ)/200000000),((-1817703143:ℚ)/2250000000),((-20508373307:ℚ)/28243750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((201233257:ℚ)/625000000),((7656816127364117046105193241863689761104871073810819295387:ℚ)/484608469042968750000000000000000000000000000000000000000000),((16500236340668851725047:ℚ)/92416000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3619576403:ℚ)/5000000000),((114316343:ℚ)/156250000),((-1426112459:ℚ)/1765234375),((-10298729209:ℚ)/14181250000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((309387939:ℚ)/1000000000),((55934253614848240058090665757054842824144063664348077471:ℚ)/3539860380136904112994670867919921875000000000000000000000),((10073781296162592160593:ℚ)/56406250000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7268847781:ℚ)/10000000000),((7345941289:ℚ)/10000000000),((-91657236757:ℚ)/113450000000),((-20686543343:ℚ)/28481250000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((2962864119:ℚ)/10000000000),((2994858272059006855769941949066622656099549411126649493638003091:ℚ)/189518484637218860156250000000000000000000000000000000000000000000),((41273836447901793280300847:ℚ)/231040000000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((1824635673:ℚ)/2500000000),((92195457:ℚ)/125000000),((-383513647:ℚ)/474687500),((-5193907019:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((113038711:ℚ)/400000000),((1072152646274902779251426259062022293113272491395221:ℚ)/67842278975296020507812500000000000000000000000000000),((6450855566823055310743:ℚ)/36100000000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7328237543:ℚ)/10000000000),((7435026911:ℚ)/10000000000),((-92815349843:ℚ)/114400000000),((-20864712629:ℚ)/28837500000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2682289403:ℚ)/10000000000),((10399442199248219459122969356338551516048982486733150681223:ℚ)/648473240897625000000000000000000000000000000000000000000000),((41308786752495078761323647:ℚ)/231040000000000000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7387627061:ℚ)/10000000000),((7494417011:ℚ)/10000000000),((-93587421143:ℚ)/115350000000),((-21042881183:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((592399033:ℚ)/2500000000),((69354937350919500880472925338645713858022038366461297033671243:ℚ)/4324849396020850781250000000000000000000000000000000000000000000),((41332141565357792292769047:ℚ)/231040000000000000000000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7447016343:ℚ)/10000000000),((7613196483:ℚ)/10000000000),((-95131554279:ℚ)/116300000000),((-21221049029:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2009842073:ℚ)/10000000000),((14154170495183261877623391340588755817887359832159273280045313:ℚ)/858487808296729687500000000000000000000000000000000000000000000),((5730439:ℚ)/32000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-13:ℚ)/16),((-3:ℚ)/4),((7565794217:ℚ)/10000000000),((7850752671:ℚ)/10000000000),((-32739928241:ℚ)/39400000000),((-21577382651:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((949119713:ℚ)/10000000000),((74042591570417793104743495645718229240586682886044188658221:ℚ)/4267264939950000000000000000000000000000000000000000000000000),((5730439:ℚ)/32000000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((7803347359:ℚ)/10000000000),((208146379:ℚ)/250000000),((-2609902927:ℚ)/3050000000),((-22290042077:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((22055990102710879233948956762657174704030855150033325641:ℚ)/1163454953906250000000000000000000000000000000000000000000),((5730439:ℚ)/32000000)⟩
theorem valid20 : Valid eighth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8278444293:ℚ)/10000000000),((5113083863:ℚ)/5000000000),((-64550090219:ℚ)/64800000000),((-23715332879:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((8919773828278730230427495262803384735818725103035958039:ℚ)/318864600000000000000000000000000000000000000000000000000),((5730439:ℚ)/32000000)⟩
theorem valid21 : Valid eighth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((5089369959:ℚ)/5000000000),((2805306923:ℚ)/2000000000),(-1:ℚ),((-14708109877:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((11694369948349283741573651:ℚ)/380880000000000000000000000),((5730439:ℚ)/32000000)⟩
theorem valid22 : Valid eighth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound eighth nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound eighth nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4481:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC04
#check @N11Formalization.C450EighthGroupedC04.bound
#print axioms N11Formalization.C450EighthGroupedC04.valid0
#print axioms N11Formalization.C450EighthGroupedC04.valid1
#print axioms N11Formalization.C450EighthGroupedC04.valid2
#print axioms N11Formalization.C450EighthGroupedC04.valid3
#print axioms N11Formalization.C450EighthGroupedC04.valid4
#print axioms N11Formalization.C450EighthGroupedC04.valid5
#print axioms N11Formalization.C450EighthGroupedC04.valid6
#print axioms N11Formalization.C450EighthGroupedC04.valid7
#print axioms N11Formalization.C450EighthGroupedC04.valid8
#print axioms N11Formalization.C450EighthGroupedC04.valid9
#print axioms N11Formalization.C450EighthGroupedC04.valid10
#print axioms N11Formalization.C450EighthGroupedC04.valid11
#print axioms N11Formalization.C450EighthGroupedC04.valid12
#print axioms N11Formalization.C450EighthGroupedC04.valid13
#print axioms N11Formalization.C450EighthGroupedC04.valid14
#print axioms N11Formalization.C450EighthGroupedC04.valid15
#print axioms N11Formalization.C450EighthGroupedC04.valid16
#print axioms N11Formalization.C450EighthGroupedC04.valid17
#print axioms N11Formalization.C450EighthGroupedC04.valid18
#print axioms N11Formalization.C450EighthGroupedC04.valid19
#print axioms N11Formalization.C450EighthGroupedC04.valid20
#print axioms N11Formalization.C450EighthGroupedC04.valid21
#print axioms N11Formalization.C450EighthGroupedC04.valid22
#print axioms N11Formalization.C450EighthGroupedC04.bound
#print axioms N11Formalization.C450EighthGroupedC04.endpoint_checks
