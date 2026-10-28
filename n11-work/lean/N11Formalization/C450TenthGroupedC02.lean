import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((6478064211:ℚ)/10000000000),((1354756191:ℚ)/2000000000),((-3859468573:ℚ)/3968000000),((-42466449477:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5502824219:ℚ)/10000000000),((50175833005353105330370641380597009225197309:ℚ)/1618189921280000000000000000000000000000000000),((525462454076146563190926509:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((134312713:ℚ)/200000000),((6892553039:ℚ)/10000000000),((-19653659117:ℚ)/20600000000),((-882588991:ℚ)/1049000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4872232419:ℚ)/10000000000),((6657055744629139312347713729347099469807527047123889078663:ℚ)/234851149126367187500000000000000000000000000000000000000000),((210630905065463127133301:ℚ)/739328000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((6834419427:ℚ)/10000000000),((217248087:ℚ)/312500000),((-619744261:ℚ)/655625000),((-44960935989:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((70735697:ℚ)/156250000),((214008976739055006261356432906619720745758865332538637919:ℚ)/7893838737634523010253906250000000000000000000000000000000),((527134470764200877056928141:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((6893810861:ℚ)/10000000000),((7011324337:ℚ)/10000000000),((-20009973011:ℚ)/21170000000),((-45376676027:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1086251531:ℚ)/2500000000),((28630299327415151437695081910243096890908989822680904559281:ℚ)/1056829975179932812500000000000000000000000000000000000000000),((527695307270225424123201709:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((6953202003:ℚ)/10000000000),((883838713:ℚ)/1250000000),((-2523516139:ℚ)/2670000000),((-45792414021:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2077742907:ℚ)/5000000000),((1794716494041840175171168044807310167613105025085421323523:ℚ)/66296346619556250000000000000000000000000000000000000000000),((528256109779591851997906861:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7012592859:ℚ)/10000000000),((88755029:ℚ)/125000000),((-253465087:ℚ)/269375000),((-15402716671:ℚ)/18037500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((158298041:ℚ)/400000000),((6738682376318013261949332235106674541825753120228520277:ℚ)/254380924906553649902343750000000000000000000000000000000),((528534598592124334984169949:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7042288183:ℚ)/10000000000),((7130094891:ℚ)/10000000000),((-20366284673:ℚ)/21645000000),((-46416017281:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3854831687:ℚ)/10000000000),((5950143534730047768395307653013898292885287943350558557826241:ℚ)/224663815698469783593750000000000000000000000000000000000000000),((528814970577461669490953781:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((3535991719:ℚ)/5000000000),((7144941159:ℚ)/10000000000),((-20410823477:ℚ)/21740000000),((-23311942033:ℚ)/27234375000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((937387273:ℚ)/2500000000),((45640623726086591993720211466670476917746508561403372204481:ℚ)/1741948808939128125000000000000000000000000000000000000000000),((132238548615177634290853269:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7086831041:ℚ)/10000000000),((7159787417:ℚ)/10000000000),((-20455362251:ℚ)/21787500000),((-46727817287:ℚ)/54587500000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((184791901:ℚ)/500000000),((164776527957805849771511765574651433411837003030925390137721:ℚ)/6289447990981832885742187500000000000000000000000000000000000),((529094373141938730792234149:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3550839313:ℚ)/5000000000),((112103651:ℚ)/156250000),((-320310953:ℚ)/341171875),((-23415875191:ℚ)/27353125000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((3641371753:ℚ)/10000000000),((181146721495668946057677102168148497337317094615079511697:ℚ)/6914819487576088869571685791015625000000000000000000000000),((132308637426098853007989701:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((1423305239:ℚ)/2000000000),((71894799:ℚ)/100000000),((-205444397:ℚ)/218825000),((-9387136673:ℚ)/10965000000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((3586115813:ℚ)/10000000000),((330008179237498707363792431509934462801289647907787823:ℚ)/12598187956546341691406250000000000000000000000000000000),((21174988965918311683809909:ℚ)/73932800000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1782843437:ℚ)/2500000000),((57634609:ℚ)/80000000),((-9688931:ℚ)/10320000),((-11759904059:ℚ)/13735937500),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((3530033057:ℚ)/10000000000),((323378391437154428724247936357516862557213252635763:ℚ)/12346026753801600000000000000000000000000000000000000),((33094681029539524145808701:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((1786555321:ℚ)/2500000000),((360958617:ℚ)/500000000),((-6923999:ℚ)/7375000),((-11785887247:ℚ)/13765625000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((3473083371:ℚ)/10000000000),((12741161820233044743448604864030865465195638548701:ℚ)/486472076473999023437500000000000000000000000000000),((33103441667999861733989589:ℚ)/115520000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7161068803:ℚ)/10000000000),((452126159:ℚ)/625000000),((-1292378477:ℚ)/1376562500),((-47247481621:ℚ)/55181250000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((1707611663:ℚ)/5000000000),((11094001318840795384661438036582783503523780669938698201521:ℚ)/423613312237029719352722167968750000000000000000000000000000),((529795234784554171972810061:ℚ)/1848320000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7175916307:ℚ)/10000000000),((7248864737:ℚ)/10000000000),((-20722594211:ℚ)/22072500000),((-47351414149:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((419550721:ℚ)/1250000000),((76890572136271210215176114982608613117059722637244364658807:ℚ)/2936207991903422167968750000000000000000000000000000000000000),((529935400762177257103083821:ℚ)/1848320000000000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3595381897:ℚ)/5000000000),((7263710921:ℚ)/10000000000),((-20767132763:ℚ)/22120000000),((-23727673279:ℚ)/27709375000),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((3296579389:ℚ)/10000000000),((2842148867687585718454775347111513375592589715021421653592177:ℚ)/108540726002438800000000000000000000000000000000000000000000000),((132518891160004530243638261:ℚ)/462080000000000000000000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1441122253:ℚ)/2000000000),((7278557093:ℚ)/10000000000),((-20811671279:ℚ)/22167500000),((-9511855771:ℚ)/11107500000),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3235688161:ℚ)/10000000000),((3909870444466089828997552069806306694596830626732277337537941:ℚ)/149327668989496097949218750000000000000000000000000000000000000),((21208629055579902868442861:ℚ)/73932800000000000000000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((45127867:ℚ)/62500000),((1458680651:ℚ)/2000000000),((-4171241953:ℚ)/4443000000),((-595790138:ℚ)/695703125),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((3173670727:ℚ)/10000000000),((45522595333365597091228488534268252457916639088942296578123:ℚ)/1738748610716737668750000000000000000000000000000000000000000),((82868107192130565378199:ℚ)/288800000000000000000000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((90441327:ℚ)/125000000),((7308249407:ℚ)/10000000000),((-20900748221:ℚ)/22262500000),((-597089289:ℚ)/697187500),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((62209193:ℚ)/200000000),((140404002577362392254484533005395583621107817483517800012471:ℚ)/5363162813250408363342285156250000000000000000000000000000000),((5180625425394263976901:ℚ)/18050000000000000000000)⟩
theorem valid18 : Valid tenth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound tenth nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((453134599:ℚ)/625000000),((7337941681:ℚ)/10000000000),((-20989825043:ℚ)/22310000000),((-2991942193:ℚ)/3500781250),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3045980553:ℚ)/10000000000),((1602331130317614828035391596030509904202467931147033243725711:ℚ)/60589975934957106250000000000000000000000000000000000000000000),((1036674487111619120988377:ℚ)/3610000000000000000000000)⟩
theorem valid19 : Valid tenth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((1455969677:ℚ)/2000000000),((3683816957:ℚ)/5000000000),((-10539450871:ℚ)/11202500000),((-9615787739:ℚ)/11250000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((2912879543:ℚ)/10000000000),((62726670763441957338688424553208412079842450468599543:ℚ)/2372403954401367187500000000000000000000000000000000000),((58842951990725497498981:ℚ)/204800000000000000000000)⟩
theorem valid20 : Valid tenth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1827385781:ℚ)/2500000000),((7397326107:ℚ)/10000000000),((-21167978321:ℚ)/22500000000),((-12071700467:ℚ)/14121875000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((2773588217:ℚ)/10000000000),((38431635091914218543669745239495987591897053575474770284202371:ℚ)/1453825407128906250000000000000000000000000000000000000000000000),((91990640165179302809829:ℚ)/320000000000000000000000)⟩
theorem valid21 : Valid tenth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3669618901:ℚ)/5000000000),((7427018261:ℚ)/10000000000),((-21257054783:ℚ)/22595000000),((-24247332307:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((2627121473:ℚ)/10000000000),((2452542526271224901250282927686829337397271561747059269838637:ℚ)/92795315949060859179687500000000000000000000000000000000000000),((132904556260993312282101629:ℚ)/462080000000000000000000000)⟩
theorem valid22 : Valid tenth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((368446621:ℚ)/500000000),((7486402453:ℚ)/10000000000),((-21435207359:ℚ)/22690000000),((-2435126347:ℚ)/2860000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((618050907:ℚ)/2500000000),((1609256938440982994533022254276806776733360186439161888701:ℚ)/59719418636985250000000000000000000000000000000000000000000),((1330451947817367566312989:ℚ)/4620800000000000000000000)⟩
theorem valid23 : Valid tenth packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7428321479:ℚ)/10000000000),((7605170387:ℚ)/10000000000),((-21791511161:ℚ)/22880000000),((-49118250353:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1064773241:ℚ)/5000000000),((2123248085276418097877908886746074548782782981348593855971553:ℚ)/75939681365433600000000000000000000000000000000000000000000000),((533256705282861151171447189:ℚ)/1848320000000000000000000000)⟩
theorem valid24 : Valid tenth packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7547098907:ℚ)/10000000000),((7723937743:ℚ)/10000000000),((-22147813229:ℚ)/23260000000),((-49949692349:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1180572771:ℚ)/10000000000),((191655520224699596720090708451265988209055263013098755611639:ℚ)/6867902466373837500000000000000000000000000000000000000000000),((533248574653560062441859421:ℚ)/1848320000000000000000000000)⟩
theorem valid25 : Valid tenth packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-15:ℚ)/16),((-7:ℚ)/8),((7665875453:ℚ)/10000000000),((1592294167:ℚ)/2000000000),((-4572082501:ℚ)/4728000000),((-832477511:ℚ)/1000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((59074097909605230437719623248718225536506895407560757:ℚ)/1981680681600000000000000000000000000000000000000000000),((18464159:ℚ)/64000000)⟩
theorem valid26 : Valid tenth packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((1580685213:ℚ)/2000000000),((1687306239:ℚ)/2000000000),((-79624897:ℚ)/80000000),((-3496265497:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((19449405562023990979014707239899381525198779936323:ℚ)/583200000000000000000000000000000000000000000000000),((18464159:ℚ)/64000000)⟩
theorem valid27 : Valid tenth packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((8378518381:ℚ)/10000000000),((2584178821:ℚ)/2500000000),(-1:ℚ),((-55769628667:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((475527546533125872928180861927244311:ℚ)/12000000000000000000000000000000000000),((18464159:ℚ)/64000000)⟩
theorem valid28 : Valid tenth packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((411151997:ℚ)/400000000),((14136931377:ℚ)/10000000000),(-1:ℚ),((-2762863979:ℚ)/4416000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((215958914969453641952543:ℚ)/4875264000000000000000000),((18464159:ℚ)/64000000)⟩
theorem valid29 : Valid tenth packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet29 valid29
private theorem node1_3 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound tenth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound tenth nn0 nn1 Qcell ((2117:ℚ)/3200) ((1087:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_7 node7_15
private theorem node16_18 :
    CellBound tenth nn0 nn1 Qcell ((8867:ℚ)/12800) ((1781:ℚ)/2560) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((1781:ℚ)/2560) :=
  cell_join leaf15 node16_18
private theorem node18_20 :
    CellBound tenth nn0 nn1 Qcell ((1781:ℚ)/2560) ((4481:ℚ)/6400) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound tenth nn0 nn1 Qcell ((1781:ℚ)/2560) ((4519:ℚ)/6400) :=
  cell_join node18_20 node20_22
private theorem node15_22 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4519:ℚ)/6400) :=
  cell_join node15_18 node18_22
private theorem node22_24 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join node22_24 node24_26
private theorem node26_28 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf26 leaf27
private theorem node28_30 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf28 leaf29
private theorem node26_30 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node26_28 node28_30
private theorem node22_30 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node22_26 node26_30
private theorem node15_30 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node15_22 node22_30
private theorem node0_30 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_30
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_30
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29]
theorem packet_count : packets.length = 30 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC02
#check @N11Formalization.C450TenthGroupedC02.bound
#print axioms N11Formalization.C450TenthGroupedC02.valid0
#print axioms N11Formalization.C450TenthGroupedC02.valid1
#print axioms N11Formalization.C450TenthGroupedC02.valid2
#print axioms N11Formalization.C450TenthGroupedC02.valid3
#print axioms N11Formalization.C450TenthGroupedC02.valid4
#print axioms N11Formalization.C450TenthGroupedC02.valid5
#print axioms N11Formalization.C450TenthGroupedC02.valid6
#print axioms N11Formalization.C450TenthGroupedC02.valid7
#print axioms N11Formalization.C450TenthGroupedC02.valid8
#print axioms N11Formalization.C450TenthGroupedC02.valid9
#print axioms N11Formalization.C450TenthGroupedC02.valid10
#print axioms N11Formalization.C450TenthGroupedC02.valid11
#print axioms N11Formalization.C450TenthGroupedC02.valid12
#print axioms N11Formalization.C450TenthGroupedC02.valid13
#print axioms N11Formalization.C450TenthGroupedC02.valid14
#print axioms N11Formalization.C450TenthGroupedC02.valid15
#print axioms N11Formalization.C450TenthGroupedC02.valid16
#print axioms N11Formalization.C450TenthGroupedC02.valid17
#print axioms N11Formalization.C450TenthGroupedC02.valid18
#print axioms N11Formalization.C450TenthGroupedC02.valid19
#print axioms N11Formalization.C450TenthGroupedC02.valid20
#print axioms N11Formalization.C450TenthGroupedC02.valid21
#print axioms N11Formalization.C450TenthGroupedC02.valid22
#print axioms N11Formalization.C450TenthGroupedC02.valid23
#print axioms N11Formalization.C450TenthGroupedC02.valid24
#print axioms N11Formalization.C450TenthGroupedC02.valid25
#print axioms N11Formalization.C450TenthGroupedC02.valid26
#print axioms N11Formalization.C450TenthGroupedC02.valid27
#print axioms N11Formalization.C450TenthGroupedC02.valid28
#print axioms N11Formalization.C450TenthGroupedC02.valid29
#print axioms N11Formalization.C450TenthGroupedC02.bound
#print axioms N11Formalization.C450TenthGroupedC02.endpoint_checks
