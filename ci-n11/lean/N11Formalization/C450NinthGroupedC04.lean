import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((6407233251:ℚ)/10000000000),((3347398261:ℚ)/5000000000),((-41276177393:ℚ)/49600000000),((-17941699753:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2839270739:ℚ)/5000000000),((606462508125231261459897344221830146647043135955726397227883:ℚ)/24272848819200000000000000000000000000000000000000000000000000),((11737773812026613604679987:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((830604421:ℚ)/1250000000),((6813595509:ℚ)/10000000000),((-84096741617:ℚ)/103000000000),((-2331813263:ℚ)/3278125000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1013524843:ℚ)/2000000000),((43786357233778257275797832330683191025977111532817134372486129:ℚ)/1878809193010937500000000000000000000000000000000000000000000000),((47017662354620712760081107:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((6763633651:ℚ)/10000000000),((433274547:ℚ)/625000000),((-5352569111:ℚ)/6556250000),((-19010900953:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4735568659:ℚ)/10000000000),((731190509200222248510609125239281688832734328821413716863:ℚ)/31391282938599014282226562500000000000000000000000000000000),((183923908343859004435023:ℚ)/902500000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((3441215107:ℚ)/5000000000),((1747947687:ℚ)/2500000000),((-21603319931:ℚ)/26700000000),((-9683645321:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4380443459:ℚ)/10000000000),((5832935882759429150614505557708963207826638122757449633121:ℚ)/258970103982641601562500000000000000000000000000000000000000),((2944878674494157654979243:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((173545697:ℚ)/250000000),((3525594171:ℚ)/5000000000),((-43592724223:ℚ)/53875000000),((-488637091:ℚ)/679375000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4192404161:ℚ)/10000000000),((26012748555334217435161469950996218311758044268710310851257311:ℚ)/1154784524082995605468750000000000000000000000000000000000000000),((11787917457753851654412627:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7001225149:ℚ)/10000000000),((7080886991:ℚ)/10000000000),((-87571530883:ℚ)/108700000000),((-19723675447:ℚ)/27293750000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((799214663:ℚ)/2000000000),((211987205405669392454928621992054204821592818781616933092638811:ℚ)/9567865261734987109375000000000000000000000000000000000000000000),((47168502645377463338636107:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7030923639:ℚ)/10000000000),((888823193:ℚ)/1250000000),((-999518319:ℚ)/1240625000),((-19812770917:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3894407611:ℚ)/10000000000),((18703653695383415098331104961450539841209228362542189791:ℚ)/844053457707452774047851562500000000000000000000000000000),((737271150899207261806403:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((441288877:ℚ)/625000000),((3570142001:ℚ)/5000000000),((-14723948671:ℚ)/18275000000),((-1243866631:ℚ)/1720703125),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((1895079419:ℚ)/5000000000),((164044000956840770113102394289774152074805746993125613951983:ℚ)/7401913400792260742187500000000000000000000000000000000000000),((11800555716980533739058347:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((1772580083:ℚ)/2500000000),((1433996473:ℚ)/2000000000),((-17745954149:ℚ)/22025000000),((-4997740249:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1841553587:ℚ)/5000000000),((3031066474692829771353937152965296407033096516094659998137:ℚ)/136748090880281066894531250000000000000000000000000000000000),((1888764411052836746875963:ℚ)/9241600000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7120018539:ℚ)/10000000000),((1439936127:ℚ)/2000000000),((-2546167093:ℚ)/3160000000),((-20080055617:ℚ)/27768750000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3573000203:ℚ)/10000000000),((7191884126343909456111419807031697796769893733204263042047:ℚ)/324423754223700000000000000000000000000000000000000000000000),((1889440635348382673054763:ℚ)/9241600000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),((-13:ℚ)/16),((-3:ℚ)/4),((1429943331:ℚ)/2000000000),((901816217:ℚ)/1250000000),((-3721203607:ℚ)/4628125000),((-4033829993:ℚ)/5565625000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((432443213:ℚ)/1250000000),((9972811875547310377116201580747269533413764751117610875769:ℚ)/453524756985326957702636718750000000000000000000000000000000),((738194929882345848322883:ℚ)/3610000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7164565679:ℚ)/10000000000),((3614689407:ℚ)/5000000000),((-44750962291:ℚ)/55656250000),((-20213697037:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((3401458683:ℚ)/10000000000),((7371473464774331122226228016963245245444157539274080394008603:ℚ)/335197675828150522708892822265625000000000000000000000000000000),((11813234922764236874032203:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2231:ℚ)/3200),((8943:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((179485367:ℚ)/250000000),((7244227869:ℚ)/10000000000),((-89694962297:ℚ)/111550000000),((-506456101:ℚ)/698671875),((961640533:ℚ)/1000000000),((9622019977:ℚ)/10000000000),((555749933:ℚ)/2000000000),((835600573:ℚ)/2500000000),((152596522861601173700008275922625928435070361181594508757320961:ℚ)/6938334007606346554687500000000000000000000000000000000000000000),((130918028862739068271947:ℚ)/640000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((8943:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8943:ℚ)/12800),((4481:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7194263659:ℚ)/10000000000),((3629538451:ℚ)/5000000000),((-44943999863:ℚ)/55893750000),((-20302790977:ℚ)/28006250000),((1922169193:ℚ)/2000000000),((1923281067:ℚ)/2000000000),((349868089:ℚ)/1250000000),((164116207:ℚ)/500000000),((159337971258244675320783496041946213542649341218632462996751:ℚ)/7244264028510430114746093750000000000000000000000000000000000),((11817470424548820486862147:ℚ)/57760000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((8943:ℚ)/12800) ((4481:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((901139077:ℚ)/1250000000),((72887749:ℚ)/100000000),((-902740737:ℚ)/1120250000),((-2543417231:ℚ)/3515625000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3221166989:ℚ)/10000000000),((20551077328636864942961854086214919086958623823827:ℚ)/926720294688034057617187500000000000000000000000000),((4728684190552818849347:ℚ)/23104000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7238810463:ℚ)/10000000000),((731847281:ℚ)/1000000000),((-9066014653:ℚ)/11250000000),((-20436431389:ℚ)/28243750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3095358481:ℚ)/10000000000),((1343492038780205001524742057474899810434054273581127372791767:ℚ)/60576058630371093750000000000000000000000000000000000000000000),((473038203140337553367467:ℚ)/2310400000000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((113570441:ℚ)/156250000),((7348170633:ℚ)/10000000000),((-91046218229:ℚ)/112975000000),((-641422646:ℚ)/886328125),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((1482196989:ℚ)/5000000000),((2572861823097662801754754899479440529075845020075813453984877:ℚ)/115994144936326073974609375000000000000000000000000000000000000),((47320816924122362048269083:ℚ)/231040000000000000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3649102949:ℚ)/5000000000),((737786837:ℚ)/1000000000),((-9143228881:ℚ)/11345000000),((-10307308847:ℚ)/14240625000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((44180571:ℚ)/156250000),((4204133043935610029836928339972382428965443143956736964383177:ℚ)/189518484637218860156250000000000000000000000000000000000000000),((473378317362068469395443:ℚ)/2310400000000000000000000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((28624623:ℚ)/39062500),((3703783011:ℚ)/5000000000),((-45909179143:ℚ)/56962500000),((-80873869:ℚ)/111718750),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((335493427:ℚ)/1250000000),((1300414259809312691648760894015918620925858742429338466517:ℚ)/58615729034655761718750000000000000000000000000000000000000),((11838716187675626761173987:ℚ)/57760000000000000000000000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3678800497:ℚ)/5000000000),((3733480537:ℚ)/5000000000),((-46295246981:ℚ)/57200000000),((-10396401491:ℚ)/14418750000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((31655177:ℚ)/125000000),((1826678157261828343152284002737198444892948679504338226119:ℚ)/81059155112203125000000000000000000000000000000000000000000),((11847246347006437655694043:ℚ)/57760000000000000000000000)⟩
theorem valid19 : Valid ninth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3708497879:ℚ)/5000000000),((7526355799:ℚ)/10000000000),((-31120875129:ℚ)/38450000000),((-10485493637:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2198943749:ℚ)/10000000000),((10829096898966077733519512233672580502696877067462540674496873:ℚ)/480538821780094531250000000000000000000000000000000000000000000),((47423178840612581561165147:ℚ)/231040000000000000000000000)⟩
theorem valid20 : Valid ninth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7476390199:ℚ)/10000000000),((7645144297:ℚ)/10000000000),((-94906875861:ℚ)/116300000000),((-21149170597:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((180603037:ℚ)/1000000000),((19926860614144915642278181809110758320321300849721836995083837:ℚ)/858487808296729687500000000000000000000000000000000000000000000),((13148387:ℚ)/64000000)⟩
theorem valid21 : Valid ninth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-13:ℚ)/16),((-3:ℚ)/4),((237349317:ℚ)/312500000),((3941358847:ℚ)/5000000000),((-48997665011:ℚ)/59100000000),((-672047951:ℚ)/953125000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((71247279:ℚ)/2000000000),((352970844484799398491873734785085010990055657878820694379961:ℚ)/14402019172331250000000000000000000000000000000000000000000000),((13148387:ℚ)/64000000)⟩
theorem valid22 : Valid ninth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((1566550097:ℚ)/2000000000),((8357851569:ℚ)/10000000000),((-104172070397:ℚ)/122000000000),((-4443650291:ℚ)/6480000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2004550913915262078653625629815832190640395009843405231474101:ℚ)/74461117050000000000000000000000000000000000000000000000000000),((13148387:ℚ)/64000000)⟩
theorem valid23 : Valid ninth packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8307882437:ℚ)/10000000000),((10258259851:ℚ)/10000000000),((-42959126021:ℚ)/43200000000),((-23643647311:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3833458722562831257970597504488141492311229063057630511:ℚ)/94478400000000000000000000000000000000000000000000000000),((13148387:ℚ)/64000000)⟩
theorem valid24 : Valid ninth packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((204165697:ℚ)/200000000),((562349563:ℚ)/400000000),(-1:ℚ),((-586897091:ℚ)/1104000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((13668450005260759471859:ℚ)/304704000000000000000000),((13148387:ℚ)/64000000)⟩
theorem valid25 : Valid ninth packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet25 valid25
private theorem node1_3 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((4367:ℚ)/6400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((4367:ℚ)/6400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound ninth nn0 nn1 Qcell ((4367:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((1781:ℚ)/2560) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound ninth nn0 nn1 Qcell ((1781:ℚ)/2560) ((8943:ℚ)/12800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((8943:ℚ)/12800) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound ninth nn0 nn1 Qcell ((4367:ℚ)/6400) ((8943:ℚ)/12800) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((8943:ℚ)/12800) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound ninth nn0 nn1 Qcell ((8943:ℚ)/12800) ((4519:ℚ)/6400) :=
  cell_join leaf13 node14_16
private theorem node17_19 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf16 node17_19
private theorem node13_19 :
    CellBound ninth nn0 nn1 Qcell ((8943:ℚ)/12800) ((143:ℚ)/200) :=
  cell_join node13_16 node16_19
private theorem node20_22 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf19 node20_22
private theorem node22_24 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node22_24 node24_26
private theorem node19_26 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node19_22 node22_26
private theorem node13_26 :
    CellBound ninth nn0 nn1 Qcell ((8943:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node13_19 node19_26
private theorem node0_26 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_26
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_26
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25]
theorem packet_count : packets.length = 26 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC04
#check @N11Formalization.C450NinthGroupedC04.bound
#print axioms N11Formalization.C450NinthGroupedC04.valid0
#print axioms N11Formalization.C450NinthGroupedC04.valid1
#print axioms N11Formalization.C450NinthGroupedC04.valid2
#print axioms N11Formalization.C450NinthGroupedC04.valid3
#print axioms N11Formalization.C450NinthGroupedC04.valid4
#print axioms N11Formalization.C450NinthGroupedC04.valid5
#print axioms N11Formalization.C450NinthGroupedC04.valid6
#print axioms N11Formalization.C450NinthGroupedC04.valid7
#print axioms N11Formalization.C450NinthGroupedC04.valid8
#print axioms N11Formalization.C450NinthGroupedC04.valid9
#print axioms N11Formalization.C450NinthGroupedC04.valid10
#print axioms N11Formalization.C450NinthGroupedC04.valid11
#print axioms N11Formalization.C450NinthGroupedC04.valid12
#print axioms N11Formalization.C450NinthGroupedC04.valid13
#print axioms N11Formalization.C450NinthGroupedC04.valid14
#print axioms N11Formalization.C450NinthGroupedC04.valid15
#print axioms N11Formalization.C450NinthGroupedC04.valid16
#print axioms N11Formalization.C450NinthGroupedC04.valid17
#print axioms N11Formalization.C450NinthGroupedC04.valid18
#print axioms N11Formalization.C450NinthGroupedC04.valid19
#print axioms N11Formalization.C450NinthGroupedC04.valid20
#print axioms N11Formalization.C450NinthGroupedC04.valid21
#print axioms N11Formalization.C450NinthGroupedC04.valid22
#print axioms N11Formalization.C450NinthGroupedC04.valid23
#print axioms N11Formalization.C450NinthGroupedC04.valid24
#print axioms N11Formalization.C450NinthGroupedC04.valid25
#print axioms N11Formalization.C450NinthGroupedC04.bound
#print axioms N11Formalization.C450NinthGroupedC04.endpoint_checks
