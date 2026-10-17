import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((1603910907:ℚ)/2500000000),((1675773653:ℚ)/2500000000),((-4707320959:ℚ)/6200000000),((-16203019977:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2828966073:ℚ)/5000000000),((1280844285225042824227459734054183958434016034099632933543:ℚ)/47407907850000000000000000000000000000000000000000000000000),((190704202067820118425839137:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((831663057:ℚ)/1250000000),((6821924457:ℚ)/10000000000),((-19185773371:ℚ)/25750000000),((-8428293627:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2522308339:ℚ)/5000000000),((750893170141494487370365144289879558763397065860441086382609:ℚ)/29356393640795898437500000000000000000000000000000000000000000),((3053577600248257259969776057:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((1354426099:ℚ)/2000000000),((6940751459:ℚ)/10000000000),((-19542254377:ℚ)/26225000000),((-13746687089:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4710994979:ℚ)/10000000000),((51381547470894678051171889812426742721116606735905781630387:ℚ)/2009042108070336914062500000000000000000000000000000000000000),((3055902314364079701752909233:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((6890953827:ℚ)/10000000000),((7000163941:ℚ)/10000000000),((-19720491823:ℚ)/26700000000),((-70040492097:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4353927799:ℚ)/10000000000),((6451936657881015668662122706045618989286962146518827635911:ℚ)/258970103982641601562500000000000000000000000000000000000000),((3057070052133864935718749633:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6950364523:ℚ)/10000000000),((7059575767:ℚ)/10000000000),((-19898727301:ℚ)/26937500000),((-70694009753:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4164724599:ℚ)/10000000000),((3597031250850719074869390847271705024323597047528523383254319:ℚ)/144348065510374450683593750000000000000000000000000000000000000),((3058241377340960840631921977:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7009774593:ℚ)/10000000000),((7089281439:ℚ)/10000000000),((-19987844317:ℚ)/27175000000),((-71347520523:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((793411879:ℚ)/2000000000),((3677823968459426600109179495243572911473017349126439105725927:ℚ)/149497894714609173583984375000000000000000000000000000000000000),((3058828385295111483418334953:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((35197397:ℚ)/50000000),((3559493477:ℚ)/5000000000),((-10038480431:ℚ)/13646875000),((-358371367:ℚ)/548250000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3864648801:ℚ)/10000000000),((469923061387069971680450823501834667113351812282108239781429:ℚ)/19098397587546533918380737304687500000000000000000000000000000),((764854072550703606220943297:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((883648007:ℚ)/1250000000),((3574346157:ℚ)/5000000000),((-10083038471:ℚ)/13706250000),((-9000128077:ℚ)/13765625000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3759593867:ℚ)/10000000000),((76847432898408980785867088710830652233606942348981847818269:ℚ)/3122682215959235000610351562500000000000000000000000000000000),((765001273022367960186309457:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((1774722141:ℚ)/2500000000),((7178397519:ℚ)/10000000000),((-20255192557:ℚ)/27531250000),((-2583134793:ℚ)/3950000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1825832941:ℚ)/5000000000),((117390896809980667636380013449058058677166669983805119277:ℚ)/4769394910724088549613952636718750000000000000000000000000),((3060594790940994672136622473:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3564296463:ℚ)/5000000000),((7208102573:ℚ)/10000000000),((-20344307719:ℚ)/27650000000),((-12109087031:ℚ)/18512500000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3540601619:ℚ)/10000000000),((764323679144091954152543182612972117941155353535602592997961:ℚ)/31048367103440039062500000000000000000000000000000000000000000),((3061185386822882530943247697:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7158297143:ℚ)/10000000000),((3618903739:ℚ)/5000000000),((-10216711217:ℚ)/13884375000),((-72981268573:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3426095571:ℚ)/10000000000),((256254809157490116108113879818948878309708907516573323746749:ℚ)/10408021380170245814323425292968750000000000000000000000000000),((765444219940316246024449153:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3594000609:ℚ)/5000000000),((1453502447:ℚ)/2000000000),((-4104507341:ℚ)/5577500000),((-36654006699:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((826947447:ℚ)/2500000000),((21447451812129729209883033991287639500130159338981163255879:ℚ)/870980904065008402343750000000000000000000000000000000000000),((122494770790502252377675337:ℚ)/591462400000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((7217705153:ℚ)/10000000000),((3648608423:ℚ)/5000000000),((-10305825269:ℚ)/14003125000),((-73634756683:ℚ)/112500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((1592630183:ℚ)/5000000000),((8558707408517379116672604990703934663029656779274771911:ℚ)/347520110508012771606445312500000000000000000000000000000),((765740639213320022627961497:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1811852237:ℚ)/2500000000),((7326921313:ℚ)/10000000000),((-20700763939:ℚ)/28125000000),((-18490374607:ℚ)/28243750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1528999541:ℚ)/5000000000),((23313551194265823819078690207039833006898637353035916824911507:ℚ)/946500916099548339843750000000000000000000000000000000000000000),((3063556741060202362968682217:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7277112607:ℚ)/10000000000),((7356625637:ℚ)/10000000000),((-20789876911:ℚ)/28243750000),((-74288238677:ℚ)/113450000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((146269393:ℚ)/500000000),((44647860991084191737716040842618545845575529228315979638669:ℚ)/1812408514630094905853271484375000000000000000000000000000000),((8487955186676684129868697:ℚ)/40960000000000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((730681613:ℚ)/1000000000),((1854008467:ℚ)/2500000000),((-5242025401:ℚ)/7090625000),((-7461497743:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((139333121:ℚ)/500000000),((9091570436275547030909631812518339353967118949598221135667:ℚ)/364498404766755676269531250000000000000000000000000000000000),((530703718249521941250857:ℚ)/2560000000000000000000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((920777847:ℚ)/1250000000),((149508831:ℚ)/200000000),((-38447863:ℚ)/52000000),((-3136185439:ℚ)/4806250000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2486731409:ℚ)/10000000000),((1519193606110646210856700158808614872014340173639:ℚ)/60900942984375000000000000000000000000000000000000),((1226616447852085989204073:ℚ)/5914624000000000000000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7425628901:ℚ)/10000000000),((3767424349:ℚ)/5000000000),((-10662273047:ℚ)/14418750000),((-75921917911:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2146245141:ℚ)/10000000000),((210731777200968946102317021747533535149694296136203725730191:ℚ)/8446971476603224182128906250000000000000000000000000000000000),((766935287914217026771993393:ℚ)/3696640000000000000000000000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7485034517:ℚ)/10000000000),((3826830721:ℚ)/5000000000),((-10840492163:ℚ)/14537500000),((-76575379687:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1741569967:ℚ)/10000000000),((4757608502720425312679715532230666667490599146743717028113:ℚ)/186303777842172241210937500000000000000000000000000000000000),((1700311:ℚ)/8192000)⟩
theorem valid18 : Valid tenth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((7603844271:ℚ)/10000000000),((7891281063:ℚ)/10000000000),((-22393843189:ℚ)/29550000000),((-77882286981:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((786986292607843012818028033387757709896328974547241595257:ℚ)/29512334369531250000000000000000000000000000000000000000000),((1700311:ℚ)/8192000)⟩
theorem valid19 : Valid tenth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((7841458191:ℚ)/10000000000),((4183249623:ℚ)/5000000000),((-11909748869:ℚ)/15250000000),((-26832013367:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((464665098108166503780249391732627124436815463794134142791:ℚ)/16159096582031250000000000000000000000000000000000000000000),((1700311:ℚ)/8192000)⟩
theorem valid20 : Valid tenth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((4158332989:ℚ)/5000000000),((10267164601:ℚ)/10000000000),((-29521493803:ℚ)/32400000000),((-42861662879:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1604451861163149022769199411031132928860549872451722811:ℚ)/39858075000000000000000000000000000000000000000000000000),((1700311:ℚ)/8192000)⟩
theorem valid21 : Valid tenth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10217299633:ℚ)/10000000000),((7033972751:ℚ)/5000000000),(-1:ℚ),((-106630295963:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((613769701015687659069497087:ℚ)/12188160000000000000000000000),((1700311:ℚ)/8192000)⟩
theorem valid22 : Valid tenth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound tenth nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((881:ℚ)/1280) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC05
#check @N11Formalization.C450TenthGroupedC05.bound
#print axioms N11Formalization.C450TenthGroupedC05.valid0
#print axioms N11Formalization.C450TenthGroupedC05.valid1
#print axioms N11Formalization.C450TenthGroupedC05.valid2
#print axioms N11Formalization.C450TenthGroupedC05.valid3
#print axioms N11Formalization.C450TenthGroupedC05.valid4
#print axioms N11Formalization.C450TenthGroupedC05.valid5
#print axioms N11Formalization.C450TenthGroupedC05.valid6
#print axioms N11Formalization.C450TenthGroupedC05.valid7
#print axioms N11Formalization.C450TenthGroupedC05.valid8
#print axioms N11Formalization.C450TenthGroupedC05.valid9
#print axioms N11Formalization.C450TenthGroupedC05.valid10
#print axioms N11Formalization.C450TenthGroupedC05.valid11
#print axioms N11Formalization.C450TenthGroupedC05.valid12
#print axioms N11Formalization.C450TenthGroupedC05.valid13
#print axioms N11Formalization.C450TenthGroupedC05.valid14
#print axioms N11Formalization.C450TenthGroupedC05.valid15
#print axioms N11Formalization.C450TenthGroupedC05.valid16
#print axioms N11Formalization.C450TenthGroupedC05.valid17
#print axioms N11Formalization.C450TenthGroupedC05.valid18
#print axioms N11Formalization.C450TenthGroupedC05.valid19
#print axioms N11Formalization.C450TenthGroupedC05.valid20
#print axioms N11Formalization.C450TenthGroupedC05.valid21
#print axioms N11Formalization.C450TenthGroupedC05.valid22
#print axioms N11Formalization.C450TenthGroupedC05.bound
#print axioms N11Formalization.C450TenthGroupedC05.endpoint_checks
