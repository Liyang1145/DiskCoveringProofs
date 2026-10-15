import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((6389164927:ℚ)/10000000000),((133480389:ℚ)/200000000),((-378041167:ℚ)/496000000),((-65160814197:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2861296881:ℚ)/5000000000),((582079423223028912001116220424486246482160220168560597:ℚ)/24272848819200000000000000000000000000000000000000000000),((3223141451332573786046749:ℚ)/17743872000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6626788031:ℚ)/10000000000),((271713301:ℚ)/400000000),((-770339903:ℚ)/1030000000),((-67774668341:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5116337301:ℚ)/10000000000),((42471000925187258315529508141540200041833178765756127391:ℚ)/1878809193010937500000000000000000000000000000000000000000),((4301817370947399879433023:ℚ)/23658496000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((1686399059:ℚ)/2500000000),((6911643353:ℚ)/10000000000),((-19614930059:ℚ)/26225000000),((-17270389649:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4787348081:ℚ)/10000000000),((45419651102421700326157623255630053635879212603894239386867:ℚ)/2009042108070336914062500000000000000000000000000000000000000),((2691345802952078682894100807:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((6864402369:ℚ)/10000000000),((6971047963:ℚ)/10000000000),((-19793143889:ℚ)/26700000000),((-70388426059:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4436036901:ℚ)/10000000000),((5691371444545069556785394286572935539717125140591593152539:ℚ)/258970103982641601562500000000000000000000000000000000000000),((2692710263463702845608448287:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((1730951173:ℚ)/2500000000),((3515226027:ℚ)/5000000000),((-9985678081:ℚ)/13468750000),((-17760462903:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4250286173:ℚ)/10000000000),((396681054041690079891223846816308498555955648143090069344353:ℚ)/18043508188796806335449218750000000000000000000000000000000000),((2020560786833175070234160701:ℚ)/11089920000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3491603269:ℚ)/5000000000),((7089855641:ℚ)/10000000000),((-20149566923:ℚ)/27175000000),((-35847635959:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1267681:ℚ)/3125000),((21675949843220380933979878853319813058794890912577065632187:ℚ)/985631368549780273437500000000000000000000000000000000000000),((2695458160076109263530667463:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((7042607917:ℚ)/10000000000),((7119557249:ℚ)/10000000000),((-20238671747:ℚ)/27412500000),((-72348687087:ℚ)/110125000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3853712663:ℚ)/10000000000),((541903169265450418698781360197100941162446545370731061110219:ℚ)/24981457727673880004882812500000000000000000000000000000000000),((2696149087584075347646135223:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7072308437:ℚ)/10000000000),((446828671:ℚ)/625000000),((-1270486013:ℚ)/1720703125),((-72675392807:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1874190633:ℚ)/5000000000),((649043232841613915682135485108884470005408471518196745950047:ℚ)/29913644880061483383178710937500000000000000000000000000000000),((10534537486242750916322743:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1775502211:ℚ)/2500000000),((897370013:ℚ)/1250000000),((-2552110039:ℚ)/3456250000),((-6083508107:ℚ)/9256250000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((72803031:ℚ)/200000000),((9212312782484766202945555731142247147100955386648865979549:ℚ)/424489393992344284057617187500000000000000000000000000000000),((42148995106027277356336687:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7131709141:ℚ)/10000000000),((7208661353:ℚ)/10000000000),((-20505984059:ℚ)/27768750000),((-73328800551:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3528756341:ℚ)/10000000000),((903700958698804359780704032527927455607565237491392816690047:ℚ)/41632085520680983257293701171875000000000000000000000000000000),((2698231358487838550617984807:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7161409329:ℚ)/10000000000),((1447672497:ℚ)/2000000000),((-179087717:ℚ)/242500000),((-73655502619:ℚ)/112025000000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((853471317:ℚ)/2500000000),((1554224308522750902390737375421608504511111402161508909:ℚ)/71585510320128906250000000000000000000000000000000000000),((323871433393486318093078021:ℚ)/1774387200000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((7191109409:ℚ)/10000000000),((7268063503:ℚ)/10000000000),((-20684190509:ℚ)/28006250000),((-73982203499:ℚ)/112500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((1647587157:ℚ)/5000000000),((7546712486552146519803146837531469682558263180463671539:ℚ)/347520110508012771606445312500000000000000000000000000000),((2699627446211333815629794007:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7220809383:ℚ)/10000000000),((3648882203:ℚ)/5000000000),((-10386646609:ℚ)/14062500000),((-74308903213:ℚ)/112975000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1586095933:ℚ)/5000000000),((2569777625767450042861447135770443058967838343049294258005659:ℚ)/118312614512443542480468750000000000000000000000000000000000000),((675081965560707997116984607:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7250509251:ℚ)/10000000000),((3663732599:ℚ)/5000000000),((-10431197797:ℚ)/14121875000),((-74635601761:ℚ)/113450000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3044419753:ℚ)/10000000000),((38450734307683991540891118821102007364651960898637504363:ℚ)/1769930190068452056497335433959960937500000000000000000000),((675257464945782191123771623:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7280209017:ℚ)/10000000000),((3678582939:ℚ)/5000000000),((-10475748817:ℚ)/14181250000),((-74962299187:ℚ)/113925000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((1455613397:ℚ)/5000000000),((8042879178854514902020936119606998263924518270903194257175561:ℚ)/370153290307068086242675781250000000000000000000000000000000000),((2026300079093060683858848349:ℚ)/11089920000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((182747717:ℚ)/250000000),((7386866449:ℚ)/10000000000),((-21040599347:ℚ)/28481250000),((-1882224887:ℚ)/2860000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1385915521:ℚ)/5000000000),((159232973430161737013567313528590954550480831508918318513:ℚ)/7326966129331970214843750000000000000000000000000000000000),((2702438599319074549308752023:ℚ)/14786560000000000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7339608241:ℚ)/10000000000),((7446267267:ℚ)/10000000000),((-21218801801:ℚ)/28600000000),((-25205230217:ℚ)/38450000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((525048793:ℚ)/2000000000),((223172577882486010333387686973681219245059619002165218459:ℚ)/10132394389025390625000000000000000000000000000000000000000),((8111560994819150849024651341:ℚ)/44359680000000000000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7399007067:ℚ)/10000000000),((469104229:ℚ)/625000000),((-1337312687:ℚ)/1802343750),((-76269077737:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2304944111:ℚ)/10000000000),((11630299558143960822455109710057600552268409446637868732599:ℚ)/527935717287701511383056640625000000000000000000000000000000),((10567480690602650847501343:ℚ)/57760000000000000000000000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7458405503:ℚ)/10000000000),((7624467231:ℚ)/10000000000),((-21753401693:ℚ)/29075000000),((-76922460533:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1933338849:ℚ)/10000000000),((33678650854696437430251506408883290401199461964271394803821:ℚ)/1490430222737377929687500000000000000000000000000000000000000),((187503141:ℚ)/1024000000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((1894300311:ℚ)/2500000000),((7862061731:ℚ)/10000000000),((-22466185193:ℚ)/29550000000),((-19557303421:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((96846163:ℚ)/1250000000),((42635272394914099030303968015936665431741541926265990859667:ℚ)/1800252396541406250000000000000000000000000000000000000000000),((187503141:ℚ)/1024000000)⟩
theorem valid19 : Valid ninth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((156295769:ℚ)/200000000),((4168617049:ℚ)/5000000000),((-11945851147:ℚ)/15250000000),((-538951153:ℚ)/864000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((415159040333046081825443737622268328810695705427099814539:ℚ)/16159096582031250000000000000000000000000000000000000000000),((187503141:ℚ)/1024000000)⟩
theorem valid20 : Valid ninth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((1036243439:ℚ)/1250000000),((1279719969:ℚ)/1250000000),((-3699159907:ℚ)/4050000000),((-10758677829:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2865471702442844806835035185277743010156797663530393:ℚ)/77847802734375000000000000000000000000000000000000000),((187503141:ℚ)/1024000000)⟩
theorem valid21 : Valid ninth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((2547608149:ℚ)/2500000000),((14038376719:ℚ)/10000000000),(-1:ℚ),((-8914563213:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3943676068818851103793491:ℚ)/84640000000000000000000000),((187503141:ℚ)/1024000000)⟩
theorem valid22 : Valid ninth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound ninth nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4481:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC05
#check @N11Formalization.C450NinthGroupedC05.bound
#print axioms N11Formalization.C450NinthGroupedC05.valid0
#print axioms N11Formalization.C450NinthGroupedC05.valid1
#print axioms N11Formalization.C450NinthGroupedC05.valid2
#print axioms N11Formalization.C450NinthGroupedC05.valid3
#print axioms N11Formalization.C450NinthGroupedC05.valid4
#print axioms N11Formalization.C450NinthGroupedC05.valid5
#print axioms N11Formalization.C450NinthGroupedC05.valid6
#print axioms N11Formalization.C450NinthGroupedC05.valid7
#print axioms N11Formalization.C450NinthGroupedC05.valid8
#print axioms N11Formalization.C450NinthGroupedC05.valid9
#print axioms N11Formalization.C450NinthGroupedC05.valid10
#print axioms N11Formalization.C450NinthGroupedC05.valid11
#print axioms N11Formalization.C450NinthGroupedC05.valid12
#print axioms N11Formalization.C450NinthGroupedC05.valid13
#print axioms N11Formalization.C450NinthGroupedC05.valid14
#print axioms N11Formalization.C450NinthGroupedC05.valid15
#print axioms N11Formalization.C450NinthGroupedC05.valid16
#print axioms N11Formalization.C450NinthGroupedC05.valid17
#print axioms N11Formalization.C450NinthGroupedC05.valid18
#print axioms N11Formalization.C450NinthGroupedC05.valid19
#print axioms N11Formalization.C450NinthGroupedC05.valid20
#print axioms N11Formalization.C450NinthGroupedC05.valid21
#print axioms N11Formalization.C450NinthGroupedC05.valid22
#print axioms N11Formalization.C450NinthGroupedC05.bound
#print axioms N11Formalization.C450NinthGroupedC05.endpoint_checks
