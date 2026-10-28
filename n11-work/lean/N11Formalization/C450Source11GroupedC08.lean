import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((3186078163:ℚ)/5000000000),((1663499811:ℚ)/2500000000),((-13531498299:ℚ)/24800000000),((-2786078163:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1152757761:ℚ)/2000000000),((1832201985261273013669508244180611692244575180670506997:ℚ)/51688441467285156250000000000000000000000000000000000000),((776213637991951501108769:ℚ)/5415000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6609946051:ℚ)/10000000000),((1693225853:ℚ)/2500000000),((-13799032677:ℚ)/25750000000),((-5809946051:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5161418717:ℚ)/10000000000),((12461330447538755433001508179018390004394565541093233557:ℚ)/362838827047729492187500000000000000000000000000000000000),((514983774724815494914359:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((1682208257:ℚ)/2500000000),((1722950521:ℚ)/2500000000),((-14066554689:ℚ)/26225000000),((-494069419:ℚ)/1112500000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4835010743:ℚ)/10000000000),((77484834867545132547599762619119948992199071783304491:ℚ)/2256812991333007812500000000000000000000000000000000000),((128473760056098692112579:ℚ)/902500000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((6847715123:ℚ)/10000000000),((6951249451:ℚ)/10000000000),((-18933748353:ℚ)/35600000000),((-6047715123:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1121730687:ℚ)/2500000000),((179587426180026523910302726710451995781521024560454963:ℚ)/5308990328758955001831054687500000000000000000000000000),((1025307781676890768851597:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6907154421:ℚ)/10000000000),((140213911:ℚ)/200000000),((-1146725199:ℚ)/2155000000),((-6107154421:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((172124353:ℚ)/400000000),((228586918761133321742687424925212310429388459564017031291:ℚ)/6757342917395019531250000000000000000000000000000000000000),((819380679417555986199:ℚ)/5776000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6966592593:ℚ)/10000000000),((1414028083:ℚ)/2000000000),((-11574252747:ℚ)/21740000000),((-6166592593:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2055811247:ℚ)/5000000000),((49313736861453520073098569499985163813859145175146166493:ℚ)/1457754069386672973632812500000000000000000000000000000000),((40925864991183043899033:ℚ)/288800000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-9:ℚ)/16),((-1:ℚ)/2),((7026029669:ℚ)/10000000000),((1419972479:ℚ)/2000000000),((-3875917437:ℚ)/7310000000),((-6226029669:ℚ)/13765625000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((977833319:ℚ)/2500000000),((100071402193107980028814533936613954402259764112836904231:ℚ)/2979375253742933273315429687500000000000000000000000000000),((40876370229967398483977:ℚ)/288800000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((1411149561:ℚ)/2000000000),((3564792039:ℚ)/5000000000),((-29203128351:ℚ)/55062500000),((-1251149561:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3807454659:ℚ)/10000000000),((183268760746247915319043201727929140305382930707246827:ℚ)/5456103667126464843750000000000000000000000000000000000),((1532057012612349869474797:ℚ)/10830000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((7085465677:ℚ)/10000000000),((1789826367:ℚ)/2500000000),((-14668437303:ℚ)/27650000000),((-6285465677:ℚ)/13884375000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3700808241:ℚ)/10000000000),((233061926302101701137030939360104691394116117753888049927:ℚ)/6938177668729448318481445312500000000000000000000000000000),((1531251156453464803215067:ℚ)/10830000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7115183289:ℚ)/10000000000),((7189026569:ℚ)/10000000000),((-19647079707:ℚ)/37025000000),((-6315183289:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3591146939:ℚ)/10000000000),((52686446538829704282723031256439617219234490429410842201:ℚ)/1568389247042751312255859375000000000000000000000000000000),((1020297543339363712596017:ℚ)/7220000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((1786225161:ℚ)/2500000000),((902343423:ℚ)/1250000000),((-7401090807:ℚ)/13943750000),((-1586225161:ℚ)/3500781250),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((695637017:ℚ)/2000000000),((401946050626749198723745710051016538593427508632899137:ℚ)/11964774175052106380462646484375000000000000000000000000),((382410622042147860032287:ℚ)/2707500000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((3587308873:ℚ)/5000000000),((3624233959:ℚ)/5000000000),((-29738105631:ℚ)/56012500000),((-1062436291:ℚ)/2343750000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3361589431:ℚ)/10000000000),((141954988913307495167764020839123592383142372124208993:ℚ)/4225422162562608718872070312500000000000000000000000000),((63701653158470010449533:ℚ)/451250000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((7204334597:ℚ)/10000000000),((3639094087:ℚ)/5000000000),((-3319094087:ℚ)/6250000000),((-6404334597:ℚ)/14121875000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3240967273:ℚ)/10000000000),((591362878195839618918083553199367878839606893992922437:ℚ)/17601800987052917480468750000000000000000000000000000000),((509345959279632943737111:ℚ)/3610000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7234051201:ℚ)/10000000000),((1461581631:ℚ)/2000000000),((-12002234679:ℚ)/22595000000),((-6434051201:ℚ)/14181250000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3115850449:ℚ)/10000000000),((6765787880817167236137567848350147762022279561762292071:ℚ)/201375163961681365966796875000000000000000000000000000000),((6430471975288850030129:ℚ)/45600000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7263767561:ℚ)/10000000000),((3683673653:ℚ)/5000000000),((-30273062877:ℚ)/56725000000),((-6463767561:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1492836683:ℚ)/5000000000),((1402826043557094437627347966837834148196425610832497461989:ℚ)/41468910518750000000000000000000000000000000000000000000000),((508895548855784919188571:ℚ)/3610000000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7323199561:ℚ)/10000000000),((7426785399:ℚ)/10000000000),((-61081068591:ℚ)/114400000000),((-6523199561:ℚ)/14418750000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2707189171:ℚ)/10000000000),((965517624674375352727632870567621154697195423568551:ℚ)/28542203264057636260986328125000000000000000000000000),((3050184321200468349247091:ℚ)/21660000000000000000000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((369131531:ℚ)/500000000),((7486222459:ℚ)/10000000000),((-20538667377:ℚ)/38450000000),((-329131531:ℚ)/726875000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((599360307:ℚ)/2500000000),((62437762821419867831662215926599383868048402949535091:ℚ)/1845803874882507324218750000000000000000000000000000000),((1015667820014773003916007:ℚ)/7220000000000000000000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7442060763:ℚ)/10000000000),((7605093583:ℚ)/10000000000),((-62685842247:ℚ)/116300000000),((-6642060763:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((255280841:ℚ)/1250000000),((7438147230467884445010918028772203248114305271169936283:ℚ)/217079316381835937500000000000000000000000000000000000000),((68373777826916717:ℚ)/486400000000000000)⟩
theorem valid17 : Valid source11 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((1512183677:ℚ)/2000000000),((1568564899:ℚ)/2000000000),((-4321694697:ℚ)/7880000000),((-1352183677:ℚ)/3050000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1014567009:ℚ)/10000000000),((3678083706332246627644107999216318626655442332291971123:ℚ)/104801383593750000000000000000000000000000000000000000000),((13637100496101243:ℚ)/97280000000000000)⟩
theorem valid18 : Valid source11 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((7798623561:ℚ)/10000000000),((8318245643:ℚ)/10000000000),((-69104210787:ℚ)/122000000000),((-6998623561:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2725837067392125230298264053348020780115058735967104680786723:ℚ)/74461117050000000000000000000000000000000000000000000000000000),((8963631:ℚ)/64000000)⟩
theorem valid19 : Valid source11 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((4136998887:ℚ)/5000000000),((2554882439:ℚ)/2500000000),((-2394882439:ℚ)/3600000000),((-3736998887:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((39139304736553317232658340397327214804159539782506677:ℚ)/874800000000000000000000000000000000000000000000000000),((8963631:ℚ)/64000000)⟩
theorem valid20 : Valid source11 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((9936659:ℚ)/9765625),((14021036571:ℚ)/10000000000),((-120429329139:ℚ)/160000000000),((-3051803:ℚ)/8984375),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((180323101757231813347425702136108247778005552980132298729491:ℚ)/3385600000000000000000000000000000000000000000000000000000000),((8963631:ℚ)/64000000)⟩
theorem valid21 : Valid source11 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet21 valid21
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
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4481:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC08
#check @N11Formalization.C450Source11GroupedC08.bound
#print axioms N11Formalization.C450Source11GroupedC08.valid0
#print axioms N11Formalization.C450Source11GroupedC08.valid1
#print axioms N11Formalization.C450Source11GroupedC08.valid2
#print axioms N11Formalization.C450Source11GroupedC08.valid3
#print axioms N11Formalization.C450Source11GroupedC08.valid4
#print axioms N11Formalization.C450Source11GroupedC08.valid5
#print axioms N11Formalization.C450Source11GroupedC08.valid6
#print axioms N11Formalization.C450Source11GroupedC08.valid7
#print axioms N11Formalization.C450Source11GroupedC08.valid8
#print axioms N11Formalization.C450Source11GroupedC08.valid9
#print axioms N11Formalization.C450Source11GroupedC08.valid10
#print axioms N11Formalization.C450Source11GroupedC08.valid11
#print axioms N11Formalization.C450Source11GroupedC08.valid12
#print axioms N11Formalization.C450Source11GroupedC08.valid13
#print axioms N11Formalization.C450Source11GroupedC08.valid14
#print axioms N11Formalization.C450Source11GroupedC08.valid15
#print axioms N11Formalization.C450Source11GroupedC08.valid16
#print axioms N11Formalization.C450Source11GroupedC08.valid17
#print axioms N11Formalization.C450Source11GroupedC08.valid18
#print axioms N11Formalization.C450Source11GroupedC08.valid19
#print axioms N11Formalization.C450Source11GroupedC08.valid20
#print axioms N11Formalization.C450Source11GroupedC08.valid21
#print axioms N11Formalization.C450Source11GroupedC08.bound
#print axioms N11Formalization.C450Source11GroupedC08.endpoint_checks
