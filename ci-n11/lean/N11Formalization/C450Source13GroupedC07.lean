import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((804602239:ℚ)/1250000000),((840823237:ℚ)/1250000000),((-752823237:ℚ)/1240000000),((-6281420151:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5605746497:ℚ)/10000000000),((1155977577982253121077829146714816647820156940974947613:ℚ)/25284217520000000000000000000000000000000000000000000000),((11656464137676110373942297:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1668678163:ℚ)/2500000000),((1369106781:ℚ)/2000000000),((-1228306781:ℚ)/2060000000),((-13098103467:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((249301289:ℚ)/500000000),((132274782744230888602105449890434129549557849852399795581:ℚ)/3006094708817500000000000000000000000000000000000000000000),((29748833938834499130776393:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((6793649271:ℚ)/10000000000),((6964474851:ℚ)/10000000000),((-6260474851:ℚ)/10490000000),((-17820947813:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4648223367:ℚ)/10000000000),((1413161709760607842666964222959892362647347736223872771:ℚ)/32104543050312500000000000000000000000000000000000000000),((742647136267931160883405513:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((1728144809:ℚ)/2500000000),((877992849:ℚ)/1250000000),((-789992849:ℚ)/1335000000),((-13633303281:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((857193159:ℚ)/2000000000),((279862009796856849805139326673980083958456579422338563:ℚ)/6474252599566040039062500000000000000000000000000000000),((11585984853327304074785313:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((871505229:ℚ)/1250000000),((3541704553:ℚ)/5000000000),((-3189704553:ℚ)/5387500000),((-6883547061:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((102341143:ℚ)/250000000),((9987017586085939085148014149387403482159020728983503026257:ℚ)/230956904816599121093750000000000000000000000000000000000000),((185241941185943154032489617:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((1406300579:ℚ)/2000000000),((1422628333:ℚ)/2000000000),((-1281828333:ℚ)/2174000000),((-1010973201:ℚ)/1985000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3892399649:ℚ)/10000000000),((5422728436894192213064468429194837952656274193016218357:ℚ)/126517226601454375000000000000000000000000000000000000000),((29615851525395501654119657:ℚ)/147865600000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7061232863:ℚ)/10000000000),((7142873833:ℚ)/10000000000),((-6438873833:ℚ)/10917500000),((-18623698589:ℚ)/36550000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3787986053:ℚ)/10000000000),((9315685106439773595321833966739081457872007598183607721113:ℚ)/217297323662751674804687500000000000000000000000000000000000),((740129051754179543752608657:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((7090962463:ℚ)/10000000000),((1434521123:ℚ)/2000000000),((-1293721123:ℚ)/2193000000),((-56138662167:ℚ)/110125000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((14723039:ℚ)/40000000),((109690214325243331528290669498407992405482722723467955027:ℚ)/2558101271313805312500000000000000000000000000000000000000),((29594478892743344715464777:ℚ)/147865600000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7120691699:ℚ)/10000000000),((900292127:ℚ)/1250000000),((-812292127:ℚ)/1376562500),((-56406225291:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3570466829:ℚ)/10000000000),((4105411906763386161781122395615279969605488622048062810163:ℚ)/95723663616196746826171875000000000000000000000000000000000),((11556172652929111784703777:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((286016823:ℚ)/400000000),((7232068041:ℚ)/10000000000),((-6528068041:ℚ)/11060000000),((-755650469:ℚ)/1481000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((54012707:ℚ)/156250000),((119335336858026306869921302905197031647694559080645291940907:ℚ)/2781933692468227500000000000000000000000000000000000000000000),((739328284120284981396988753:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7180149097:ℚ)/10000000000),((3630899347:ℚ)/5000000000),((-1092966449:ℚ)/1851250000),((-56941341873:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((417431919:ℚ)/1250000000),((105849587590738079196978447328651770736301320122981386739:ℚ)/2467086549373687896728515625000000000000000000000000000000),((184765418813725311980285417:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7209877269:ℚ)/10000000000),((364576449:ℚ)/500000000),((-329376449:ℚ)/557750000),((-57208895421:ℚ)/112025000000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3217987327:ℚ)/10000000000),((7475213205654324460639552239356502623777193588405071689:ℚ)/174196180813001680468750000000000000000000000000000000000),((1846988057877425363171713:ℚ)/9241600000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((1447921019:ℚ)/2000000000),((915157363:ℚ)/1250000000),((-827157363:ℚ)/1400312500),((-3831763057:ℚ)/7500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3091924229:ℚ)/10000000000),((5303349527096613774356283359630187937271588035089143:ℚ)/123562705958404541015625000000000000000000000000000000),((607342868230471458658163:ℚ)/3040000000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((363466629:ℚ)/500000000),((1845179421:ℚ)/2500000000),((-1669179421:ℚ)/2812500000),((-2887199661:ℚ)/5672500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2960678549:ℚ)/10000000000),((15499687035890988093159982464318927110870952813471116221:ℚ)/357928769016265869140625000000000000000000000000000000000),((46143803353144561561081033:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7328786543:ℚ)/10000000000),((744017507:ℚ)/1000000000),((-673617507:ℚ)/1134500000),((-58279078887:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((133978119:ℚ)/500000000),((808336270904323529510570597095700316116748702326700149:ℚ)/18662318324057890625000000000000000000000000000000000000),((7377693524398269708193737:ℚ)/36966400000000000000000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((923529899:ℚ)/1250000000),((1889771449:ℚ)/2500000000),((-131828573:ℚ)/220000000),((-7351769091:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((236616263:ℚ)/1000000000),((72098104169007345562831325050981487289023530906385783:ℚ)/1636608490000000000000000000000000000000000000000000000),((46082268225636967451601713:ℚ)/231040000000000000000000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((3753570339:ℚ)/5000000000),((1535598269:ℚ)/2000000000),((-1394798269:ℚ)/2326000000),((-9980711017:ℚ)/19700000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((156481913:ℚ)/1000000000),((6723472974395972728805426407711402243714138129469080229:ℚ)/152620054808307500000000000000000000000000000000000000000),((24215594833160629:ℚ)/121600000000000000)⟩
theorem valid16 : Valid source13 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((1525207457:ℚ)/2000000000),((197894697:ℚ)/250000000),((-180294697:ℚ)/295500000),((-12190867113:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((16358321912978978767015206362392718059310657456210351:ℚ)/360050479308281250000000000000000000000000000000000000),((50914427:ℚ)/256000000)⟩
theorem valid17 : Valid source13 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((314552671:ℚ)/400000000),((4195664347:ℚ)/5000000000),((-3843664347:ℚ)/6100000000),((-841258013:ℚ)/1728000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((9921174171370293083024597462551251667921332870935360803:ℚ)/206836436250000000000000000000000000000000000000000000000),((50914427:ℚ)/256000000)⟩
theorem valid18 : Valid source13 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4169663253:ℚ)/5000000000),((10292977537:ℚ)/10000000000),((-9588977537:ℚ)/12960000000),((-33686969277:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((502115157311713101161113941197197129821824661471318211:ℚ)/8162933760000000000000000000000000000000000000000000000),((50914427:ℚ)/256000000)⟩
theorem valid19 : Valid source13 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10240880619:ℚ)/10000000000),((3523728027:ℚ)/2500000000),((-3347728027:ℚ)/4000000000),((-28162641857:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2391481465749153997902409731065243671150890740383252529:ℚ)/31740000000000000000000000000000000000000000000000000000),((50914427:ℚ)/256000000)⟩
theorem valid20 : Valid source13 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4443:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4443:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((4443:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC07
#check @N11Formalization.C450Source13GroupedC07.bound
#print axioms N11Formalization.C450Source13GroupedC07.valid0
#print axioms N11Formalization.C450Source13GroupedC07.valid1
#print axioms N11Formalization.C450Source13GroupedC07.valid2
#print axioms N11Formalization.C450Source13GroupedC07.valid3
#print axioms N11Formalization.C450Source13GroupedC07.valid4
#print axioms N11Formalization.C450Source13GroupedC07.valid5
#print axioms N11Formalization.C450Source13GroupedC07.valid6
#print axioms N11Formalization.C450Source13GroupedC07.valid7
#print axioms N11Formalization.C450Source13GroupedC07.valid8
#print axioms N11Formalization.C450Source13GroupedC07.valid9
#print axioms N11Formalization.C450Source13GroupedC07.valid10
#print axioms N11Formalization.C450Source13GroupedC07.valid11
#print axioms N11Formalization.C450Source13GroupedC07.valid12
#print axioms N11Formalization.C450Source13GroupedC07.valid13
#print axioms N11Formalization.C450Source13GroupedC07.valid14
#print axioms N11Formalization.C450Source13GroupedC07.valid15
#print axioms N11Formalization.C450Source13GroupedC07.valid16
#print axioms N11Formalization.C450Source13GroupedC07.valid17
#print axioms N11Formalization.C450Source13GroupedC07.valid18
#print axioms N11Formalization.C450Source13GroupedC07.valid19
#print axioms N11Formalization.C450Source13GroupedC07.valid20
#print axioms N11Formalization.C450Source13GroupedC07.bound
#print axioms N11Formalization.C450Source13GroupedC07.endpoint_checks
