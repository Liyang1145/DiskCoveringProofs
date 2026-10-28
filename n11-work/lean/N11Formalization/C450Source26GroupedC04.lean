import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((860924769:ℚ)/1250000000),((7104300843:ℚ)/10000000000),((-76995910959:ℚ)/99200000000),((-2082774307:ℚ)/3159375000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2182503641:ℚ)/5000000000),((1742692679149822499519295519852565958031402104186744502535458719:ℚ)/6236161374412800000000000000000000000000000000000000000000000000),((9014504326757459628526309:ℚ)/13862400000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1401352799:ℚ)/2000000000),((223872743:ℚ)/312500000),((-2430345659:ℚ)/3159375000),((-3404058397:ℚ)/5102500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((3977299199:ℚ)/10000000000),((139515392477774666636355680693205475639808131186984891631:ℚ)/513156194654036879539489746093750000000000000000000000000),((7696631813583244776908023:ℚ)/11829248000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1766609563:ℚ)/2500000000),((7193739481:ℚ)/10000000000),((-78158613253:ℚ)/102050000000),((-4299828689:ℚ)/6407812500),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((1884710811:ℚ)/5000000000),((832289056658191540523567968912294214784097959796392741148068157:ℚ)/3103102222103236132812500000000000000000000000000000000000000000),((12029233784982887509251487:ℚ)/18483200000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((1419254657:ℚ)/2000000000),((3611775017:ℚ)/5000000000),((-39273075221:ℚ)/51262500000),((-3457763971:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3661290033:ℚ)/10000000000),((7190129786711316715839131237159734380986929272705008997155863:ℚ)/26796314625414147949218750000000000000000000000000000000000000),((7702731817345309024739127:ℚ)/11829248000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7126106947:ℚ)/10000000000),((7253359449:ℚ)/10000000000),((-78933672837:ℚ)/103000000000),((-17378320841:ℚ)/25868750000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((887506027:ℚ)/2500000000),((314068106688733288101250971860409343217856501893303316750663757:ℚ)/1169991062647937500000000000000000000000000000000000000000000000),((192668639447647679346589807:ℚ)/295731200000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((3577969629:ℚ)/5000000000),((1453652747:ℚ)/2000000000),((-15825485711:ℚ)/20695000000),((-8733908887:ℚ)/12964062500),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((34353187:ℚ)/100000000),((1016864203868844390599943192292804978942696102638901083559527519:ℚ)/3813453804029939352343750000000000000000000000000000000000000000),((7606337612832053075060191:ℚ)/11673600000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7002788:ℚ)/9765625),((14224937:ℚ)/19531250),((-2478786896:ℚ)/3241015625),((-547267648:ℚ)/812109375),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((3376566873:ℚ)/10000000000),((1393672707324184535852599967566099331870746180164351941491:ℚ)/5225401944315944868139922618865966796875000000000000000000),((735259533637944038273:ℚ)/1128125000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-13:ℚ)/16),((-3:ℚ)/4),((1437154047:ℚ)/2000000000),((291922859:ℚ)/400000000),((-289145197:ℚ)/378000000),((-3511462141:ℚ)/5209375000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((3316816367:ℚ)/10000000000),((187682847033724532588164755388266496677138440520302341991:ℚ)/703538518505287500000000000000000000000000000000000000000),((23135257379514018987130021:ℚ)/35487744000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((720068523:ℚ)/1000000000),((7312974933:ℚ)/10000000000),((-79708674129:ℚ)/104187500000),((-1760205569:ℚ)/2610625000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((1628006061:ℚ)/5000000000),((8226728000156488015157286292930210594518987610038243753656269169:ℚ)/30831583325455027389526367187500000000000000000000000000000000000),((5785310854355420230247101:ℚ)/8871936000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((3607799949:ℚ)/5000000000),((7327878117:ℚ)/10000000000),((-79902415521:ℚ)/104425000000),((-8823399847:ℚ)/13082812500),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((638818777:ℚ)/2000000000),((33290520455983012725291905401615632563352354767749504346988033721:ℚ)/124737104962953077563476562500000000000000000000000000000000000000),((144670144597793004802469869:ℚ)/221798400000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3615257121:ℚ)/5000000000),((7342781031:ℚ)/10000000000),((-26698717801:ℚ)/34887500000),((-8845771363:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1565497741:ℚ)/5000000000),((19489383708025197281746347173979570847341830836074441565021281:ℚ)/73009697811792208862304687500000000000000000000000000000000000),((144707478352524989266502629:ℚ)/221798400000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((905678533:ℚ)/1250000000),((3686293027:ℚ)/5000000000),((-40241809351:ℚ)/52450000000),((-2217035599:ℚ)/3292968750),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((191665249:ℚ)/625000000),((1723033301620472377683566188198691744566190384989880359399111:ℚ)/6408725116337507812500000000000000000000000000000000000000000),((3016686069839752957633247:ℚ)/4620800000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7275255351:ℚ)/10000000000),((14457793:ℚ)/19531250),((-1263610472:ℚ)/1646484375),((-17825766053:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((2933849943:ℚ)/10000000000),((89669846680013761431153537818143549982165178720922583244593:ℚ)/333398242865220084786415100097656250000000000000000000000000),((579501597980049925384121269:ℚ)/887193600000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7305081177:ℚ)/10000000000),((7432192931:ℚ)/10000000000),((-81258508103:ℚ)/105850000000),((-17915243531:ℚ)/26581250000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((279494941:ℚ)/1000000000),((36073151355807959876413021418143411283027794965536983715949235687:ℚ)/134073630591847278906250000000000000000000000000000000000000000000),((579798839284106681492649301:ℚ)/887193600000000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((3667452879:ℚ)/5000000000),((3730997407:ℚ)/5000000000),((-40822966291:ℚ)/53162500000),((-9002358637:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((1324490611:ℚ)/5000000000),((4504572788200155683159699801373778534718831591674143603106531:ℚ)/16736272403030557250976562500000000000000000000000000000000000),((145023862386086085238922629:ℚ)/221798400000000000000000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((920591139:ℚ)/1250000000),((7521595537:ℚ)/10000000000),((-82420741981:ℚ)/106800000000),((-2261773417:ℚ)/3367187500),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((623676069:ℚ)/2500000000),((4522502691128530604464395790987949860476207723839909429203247:ℚ)/16574086654889062500000000000000000000000000000000000000000000),((9075634764521355989473549:ℚ)/13862400000000000000000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7424372201:ℚ)/10000000000),((1895298073:ℚ)/2500000000),((-20798874949:ℚ)/26937500000),((-18273116603:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((215399523:ℚ)/1000000000),((39407727714685174859749593950954007616229728130526341020134469:ℚ)/144348065510374450683593750000000000000000000000000000000000000),((193810220746799445071578023:ℚ)/295731200000000000000000000)⟩
theorem valid16 : Valid source26 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7484010573:ℚ)/10000000000),((962546789:ℚ)/1250000000),((-10593108257:ℚ)/13587500000),((-18452031719:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1749328201:ℚ)/10000000000),((62971234903674393034495137957223936754108479342299469602691:ℚ)/224745100082546424865722656250000000000000000000000000000000),((581403393064014901929576301:ℚ)/887193600000000000000000000)⟩
theorem valid17 : Valid source26 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((1520654731:ℚ)/2000000000),((3969347539:ℚ)/5000000000),((-43921518007:ℚ)/55300000000),((-289381861:ℚ)/440000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((37598257566175055430452868078250393849124806682432439637247:ℚ)/127891235106250000000000000000000000000000000000000000000000),((335175357:ℚ)/512000000)⟩
theorem valid18 : Valid source26 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((3920874189:ℚ)/5000000000),((8891494757:ℚ)/10000000000),((-9111766531:ℚ)/10400000000),((-9762622567:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1428388709008098384751163139007705748293951153723176296897:ℚ)/3843871200000000000000000000000000000000000000000000000000),((335175357:ℚ)/512000000)⟩
theorem valid19 : Valid source26 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8795072753:ℚ)/10000000000),((5397746677:ℚ)/5000000000),((-62490706801:ℚ)/64800000000),((-22385218259:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((144687265890238493791523113515489640939381002928025719907:ℚ)/318864600000000000000000000000000000000000000000000000000),((335175357:ℚ)/512000000)⟩
theorem valid20 : Valid source26 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((2139963927:ℚ)/2000000000),((584007253:ℚ)/400000000),(-1:ℚ),((-5619891781:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((31492879369682111247014951:ℚ)/60940800000000000000000000),((335175357:ℚ)/512000000)⟩
theorem valid21 : Valid source26 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((4101:ℚ)/6400) ((4139:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source26 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4139:ℚ)/6400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((4139:ℚ)/6400) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source26 nn0 nn1 Qcell ((8297:ℚ)/12800) ((1667:ℚ)/2560) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((1667:ℚ)/2560) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source26 nn0 nn1 Qcell ((1667:ℚ)/2560) ((1049:ℚ)/1600) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source26 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((143:ℚ)/200) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC04
#check @N11Formalization.C450Source26GroupedC04.bound
#print axioms N11Formalization.C450Source26GroupedC04.valid0
#print axioms N11Formalization.C450Source26GroupedC04.valid1
#print axioms N11Formalization.C450Source26GroupedC04.valid2
#print axioms N11Formalization.C450Source26GroupedC04.valid3
#print axioms N11Formalization.C450Source26GroupedC04.valid4
#print axioms N11Formalization.C450Source26GroupedC04.valid5
#print axioms N11Formalization.C450Source26GroupedC04.valid6
#print axioms N11Formalization.C450Source26GroupedC04.valid7
#print axioms N11Formalization.C450Source26GroupedC04.valid8
#print axioms N11Formalization.C450Source26GroupedC04.valid9
#print axioms N11Formalization.C450Source26GroupedC04.valid10
#print axioms N11Formalization.C450Source26GroupedC04.valid11
#print axioms N11Formalization.C450Source26GroupedC04.valid12
#print axioms N11Formalization.C450Source26GroupedC04.valid13
#print axioms N11Formalization.C450Source26GroupedC04.valid14
#print axioms N11Formalization.C450Source26GroupedC04.valid15
#print axioms N11Formalization.C450Source26GroupedC04.valid16
#print axioms N11Formalization.C450Source26GroupedC04.valid17
#print axioms N11Formalization.C450Source26GroupedC04.valid18
#print axioms N11Formalization.C450Source26GroupedC04.valid19
#print axioms N11Formalization.C450Source26GroupedC04.valid20
#print axioms N11Formalization.C450Source26GroupedC04.valid21
#print axioms N11Formalization.C450Source26GroupedC04.bound
#print axioms N11Formalization.C450Source26GroupedC04.endpoint_checks
