import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6637285347:ℚ)/10000000000),((1706931387:ℚ)/2500000000),((-19790108031:ℚ)/24800000000),((-17351856041:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((318003429:ℚ)/625000000),((3260854947563811596825032112555856367715647436010968167392127:ℚ)/48720010737600000000000000000000000000000000000000000000000000),((19443651592906630939104901723:ℚ)/44359680000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((3378137387:ℚ)/5000000000),((3473339629:ℚ)/5000000000),((-40353415177:ℚ)/50550000000),((-8854412161:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2378378197:ℚ)/5000000000),((859646007574819590805168801015611289077923305286464970091403:ℚ)/12847221313569140625000000000000000000000000000000000000000000),((1623171406066712254775645881:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((6875255343:ℚ)/10000000000),((7006153313:ℚ)/10000000000),((-81479993069:ℚ)/103000000000),((-18065766029:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((550330947:ℚ)/1250000000),((21649400417186068900268010994368865107677703976237201869857207:ℚ)/335442431903906250000000000000000000000000000000000000000000000),((19493618897757448544449852003:ℚ)/44359680000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6934742457:ℚ)/10000000000),((7065625569:ℚ)/10000000000),((-3046412311:ℚ)/3850000000),((-18244227371:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((168609933:ℚ)/400000000),((3167216787648841063027098773637111472618374145367636242447:ℚ)/49059508762988281250000000000000000000000000000000000000000),((19510771052829259565427264403:ℚ)/44359680000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((1398845507:ℚ)/2000000000),((7095361039:ℚ)/10000000000),((-82639693507:ℚ)/104900000000),((-3684536521:ℚ)/5268750000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((4019673327:ℚ)/10000000000),((1625826357027207868478310845520050578338240771281424814517371:ℚ)/25634900465350031250000000000000000000000000000000000000000000),((260246887332529826550734601:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((438998083:ℚ)/625000000),((1781274019:ℚ)/2500000000),((-20756562247:ℚ)/26343750000),((-1156994249:ℚ)/1653906250),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((979609541:ℚ)/2500000000),((186703720615562979432563262497338989362338121912414470258073:ℚ)/2943101730120563507080078125000000000000000000000000000000000),((25425885448640233282110761:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((881713829:ℚ)/1250000000),((223588459:ℚ)/312500000),((-2606649967:ℚ)/3307812500),((-2325141487:ℚ)/3322656250),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((476832663:ℚ)/1250000000),((129811524036140921792222793232038966438830629574225942155131:ℚ)/2045801248044544661045074462890625000000000000000000000000000),((5355164436003933303088611:ℚ)/12160000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((3541725727:ℚ)/5000000000),((89807061:ℚ)/125000000),((-1047491793:ℚ)/1329062500),((-9345177181:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3708128847:ℚ)/10000000000),((2074615817959252519652810338127277470071963604389550651:ℚ)/32688032037169057130813598632812500000000000000000000000),((1628683005454609847575501121:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((35565959:ℚ)/50000000),((7214298657:ℚ)/10000000000),((-28061960847:ℚ)/35600000000),((-93897877:ℚ)/134093750),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((899648889:ℚ)/2500000000),((2575028986775786101569436463246547921142189315155791311265079:ℚ)/40563654099653125000000000000000000000000000000000000000000000),((162939571957293346609169:ℚ)/369664000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7142931677:ℚ)/10000000000),((451822837:ℚ)/625000000),((-5273696881:ℚ)/6704687500),((-18868795031:ℚ)/26878125000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((435722253:ℚ)/1250000000),((22838454392379720915588908936923951155671957190900326874779:ℚ)/362896107553176294453442096710205078125000000000000000000000),((6518867268110253024125877321:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((3578900721:ℚ)/5000000000),((289761281:ℚ)/400000000),((-3382896653:ℚ)/4300500000),((-9456702163:ℚ)/13468750000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3428036539:ℚ)/10000000000),((34055301911298663166259167609475684615853144735199147343:ℚ)/541056610379789250183105468750000000000000000000000000000),((4890218735921711790709045027:ℚ)/11089920000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((1793167773:ℚ)/2500000000),((3629449279:ℚ)/5000000000),((-42382840627:ℚ)/53875000000),((-4739503319:ℚ)/6749218750),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((1684672907:ℚ)/5000000000),((573954789580845534060002181271148961897730971344670647410081931:ℚ)/9117564154864671325683593750000000000000000000000000000000000000),((1222821698490287206597750363:ℚ)/2772480000000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7187540627:ℚ)/10000000000),((727376499:ℚ)/1000000000),((-8495894487:ℚ)/10798750000),((-19002621881:ℚ)/27056250000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1654827643:ℚ)/5000000000),((290188745607020794834500009982875003405931295017374913672511:ℚ)/4609201257395839568710327148437500000000000000000000000000000),((6523139500169511770869036521:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7202410049:ℚ)/10000000000),((1825874389:ℚ)/2500000000),((-21336367057:ℚ)/27056250000),((-19047230147:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3248909773:ℚ)/10000000000),((41850934688048746034715468464343937612433190334657949163431:ℚ)/658853626180290985107421875000000000000000000000000000000000),((6526128186755384008159528449:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1446429711:ℚ)/2000000000),((733322973:ℚ)/1000000000),((-8573198649:ℚ)/10870000000),((-3827289133:ℚ)/5458750000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((781001571:ℚ)/2500000000),((27630795564847438682750598973902466444326076251448391604003:ℚ)/434902966442499414062500000000000000000000000000000000000000),((783476904542321446238557987:ℚ)/1774387200000000000000000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7261886617:ℚ)/10000000000),((1472592303:ℚ)/2000000000),((-17223699939:ℚ)/21835000000),((-19225659851:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((2994075687:ℚ)/10000000000),((57801821655781841060279667222647710794778161805436557988921:ℚ)/909616703704541894531250000000000000000000000000000000000000),((6531819013824797136874910961:ℚ)/14786560000000000000000000000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((7291624239:ℚ)/10000000000),((3696346459:ℚ)/5000000000),((-43252503967:ℚ)/54825000000),((-19314872717:ℚ)/27531250000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((2858431917:ℚ)/10000000000),((6350973080153711537556943991166114859554161457024642916607671:ℚ)/99925830910695520019531250000000000000000000000000000000000000),((19603987846267751102171481187:ℚ)/44359680000000000000000000000)⟩
theorem valid16 : Valid source17 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source17 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((1830340357:ℚ)/2500000000),((7422423943:ℚ)/10000000000),((-86891511259:ℚ)/110125000000),((-4851021071:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1358109263:ℚ)/5000000000),((3803107546439753148155223165396065287958545192624377450315721:ℚ)/59827289760122966766357421875000000000000000000000000000000000),((21504950689861700731593379:ℚ)/48640000000000000000000000)⟩
theorem valid17 : Valid source17 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source17 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7351098189:ℚ)/10000000000),((3740942439:ℚ)/5000000000),((-43832251707:ℚ)/55300000000),((-19493294567:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((641585723:ℚ)/2500000000),((1518424215434764234833792524534013947561508400846438592107373:ℚ)/23485863557396679687500000000000000000000000000000000000000000),((19630429186183313508051259387:ℚ)/44359680000000000000000000000)⟩
theorem valid18 : Valid source17 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((7410570449:ℚ)/10000000000),((3770672179:ℚ)/5000000000),((-44218738327:ℚ)/55775000000),((-19671711347:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1118686213:ℚ)/5000000000),((114363087260878603833402050734876715079975776273961367:ℚ)/1768650730705261230468750000000000000000000000000000000),((6549155075877037131464969249:ℚ)/14786560000000000000000000000)⟩
theorem valid19 : Valid source17 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((7470041063:ℚ)/10000000000),((7660259101:ℚ)/10000000000),((-89983368313:ℚ)/112500000000),((-1526932553:ℚ)/2200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((925981043:ℚ)/5000000000),((3267411901986469710446529942700357766759051676664362975491:ℚ)/48944091796875000000000000000000000000000000000000000000000),((6554744452994619227925533681:ℚ)/14786560000000000000000000000)⟩
theorem valid20 : Valid source17 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((1517795503:ℚ)/2000000000),((8611402847:ℚ)/10000000000),((-102348237011:ℚ)/114400000000),((-4041386509:ℚ)/6480000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((538642311:ℚ)/10000000000),((242305139136510651451271000852655435508979882295524881172129:ℚ)/2558096283600000000000000000000000000000000000000000000000000),((262142315986819140446564641:ℚ)/591462400000000000000000000)⟩
theorem valid21 : Valid source17 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((4270135967:ℚ)/5000000000),((10513037579:ℚ)/10000000000),((-127069488527:ℚ)/129600000000),((-11530407901:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((151547308772922340501339937382676669965402565458713417837:ℚ)/1275458400000000000000000000000000000000000000000000000000),((453839819:ℚ)/1024000000)⟩
theorem valid22 : Valid source17 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((5221060947:ℚ)/5000000000),((7157477801:ℚ)/5000000000),(-1:ℚ),((-14383182841:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((12852634212537535585318523:ℚ)/95220000000000000000000000),((453839819:ℚ)/1024000000)⟩
theorem valid23 : Valid source17 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet23 valid23
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source17 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((8601:ℚ)/12800) ((8639:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8639:ℚ)/12800) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8639:ℚ)/12800) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((8639:ℚ)/12800) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source17 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4367:ℚ)/6400) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source17 nn0 nn1 Qcell ((4367:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source17 nn0 nn1 Qcell ((8639:ℚ)/12800) ((553:ℚ)/800) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf18 node19_21
private theorem node22_24 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf21 node22_24
private theorem node18_24 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node18_21 node21_24
private theorem node12_24 :
    CellBound source17 nn0 nn1 Qcell ((8639:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node12_18 node18_24
private theorem node0_24 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_24
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_24
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23]
theorem packet_count : packets.length = 24 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC04
#check @N11Formalization.C450Source17GroupedC04.bound
#print axioms N11Formalization.C450Source17GroupedC04.valid0
#print axioms N11Formalization.C450Source17GroupedC04.valid1
#print axioms N11Formalization.C450Source17GroupedC04.valid2
#print axioms N11Formalization.C450Source17GroupedC04.valid3
#print axioms N11Formalization.C450Source17GroupedC04.valid4
#print axioms N11Formalization.C450Source17GroupedC04.valid5
#print axioms N11Formalization.C450Source17GroupedC04.valid6
#print axioms N11Formalization.C450Source17GroupedC04.valid7
#print axioms N11Formalization.C450Source17GroupedC04.valid8
#print axioms N11Formalization.C450Source17GroupedC04.valid9
#print axioms N11Formalization.C450Source17GroupedC04.valid10
#print axioms N11Formalization.C450Source17GroupedC04.valid11
#print axioms N11Formalization.C450Source17GroupedC04.valid12
#print axioms N11Formalization.C450Source17GroupedC04.valid13
#print axioms N11Formalization.C450Source17GroupedC04.valid14
#print axioms N11Formalization.C450Source17GroupedC04.valid15
#print axioms N11Formalization.C450Source17GroupedC04.valid16
#print axioms N11Formalization.C450Source17GroupedC04.valid17
#print axioms N11Formalization.C450Source17GroupedC04.valid18
#print axioms N11Formalization.C450Source17GroupedC04.valid19
#print axioms N11Formalization.C450Source17GroupedC04.valid20
#print axioms N11Formalization.C450Source17GroupedC04.valid21
#print axioms N11Formalization.C450Source17GroupedC04.valid22
#print axioms N11Formalization.C450Source17GroupedC04.valid23
#print axioms N11Formalization.C450Source17GroupedC04.bound
#print axioms N11Formalization.C450Source17GroupedC04.endpoint_checks
