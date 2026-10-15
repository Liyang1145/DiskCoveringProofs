import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6805054653:ℚ)/10000000000),((3506445323:ℚ)/5000000000),((-38863789199:ℚ)/49600000000),((-16895163959:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4614632579:ℚ)/10000000000),((4488637303077101862948113122319325892446310134702886848087407:ℚ)/21653338105600000000000000000000000000000000000000000000000000),((3221870059456888512578337433:ℚ)/5544960000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3462137649:ℚ)/5000000000),((442028779:ℚ)/625000000),((-4906374127:ℚ)/6318750000),((-8626412947:ℚ)/12756250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4248784231:ℚ)/10000000000),((407197444375030066158403340855137451876884838696057197:ℚ)/2024284791534662246704101562500000000000000000000000000),((42419207204857625901065323:ℚ)/72960000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((6983879011:ℚ)/10000000000),((713202667:ℚ)/1000000000),((-7927634671:ℚ)/10205000000),((-17431637033:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4054336393:ℚ)/10000000000),((3543887107342877393443081558597686918264046756211122924807:ℚ)/17617062804079882812500000000000000000000000000000000000000),((1075753012820374260890643059:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((88043481:ℚ)/125000000),((143236169:ℚ)/200000000),((-1593270197:ℚ)/2060000000),((-220130443:ℚ)/323359375),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((15402657:ℚ)/40000000),((463824113222460030235818784804978186298200482063967702229:ℚ)/2339982125295875000000000000000000000000000000000000000000),((504409826275363932761557:ℚ)/866400000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7073276661:ℚ)/10000000000),((1438317873:ℚ)/2000000000),((-16010132349:ℚ)/20695000000),((-1609075453:ℚ)/2362500000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((936225017:ℚ)/2500000000),((908025929077579332354726181715153950922898455997577305511:ℚ)/4580534632321142578125000000000000000000000000000000000000),((169995347178602186604768883:ℚ)/291840000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((221971057:ℚ)/312500000),((288854777:ℚ)/400000000),((-3217512101:ℚ)/4158000000),((-1111826342:ℚ)/1631640625),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3636213631:ℚ)/10000000000),((267582379455496172343129545734586728896083512479873733439:ℚ)/1349695547411990625000000000000000000000000000000000000000),((2103904401664402608521717:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((222902187:ℚ)/312500000),((7236259139:ℚ)/10000000000),((-80631368807:ℚ)/104425000000),((-2234826244:ℚ)/3270703125),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((3524334023:ℚ)/10000000000),((681959271055388672092394820008381756041568820104883441193792399:ℚ)/3464919582304252154541015625000000000000000000000000000000000000),((6312633263100125332982681:ℚ)/10830000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7147767693:ℚ)/10000000000),((1812787161:ℚ)/2500000000),((-6735411031:ℚ)/8721875000),((-17923303079:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((433387543:ℚ)/1250000000),((56135019070962644772328713166969050438201311069534400379607:ℚ)/285194132077313315868377685546875000000000000000000000000000),((3232908280352945781510883513:ℚ)/5544960000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((1432533031:ℚ)/2000000000),((7266037941:ℚ)/10000000000),((-81018493233:ℚ)/104900000000),((-3593599093:ℚ)/5256875000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((3408946281:ℚ)/10000000000),((148619529170303065080446905916221745416803077924026611822203289:ℚ)/755014082120689062500000000000000000000000000000000000000000000),((43116633927447040952901419:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((3588781187:ℚ)/5000000000),((910115879:ℚ)/1250000000),((-10151506427:ℚ)/13142187500),((-9006343561:ℚ)/13171875000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((3349823819:ℚ)/10000000000),((551294355338397403565436480330409406368098877891125321919:ℚ)/2800500424281256854534149169921875000000000000000000000000),((269548835285420114573392051:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((143849187:ℚ)/200000000),((3647907959:ℚ)/5000000000),((-40702803467:ℚ)/52687500000),((-361147561:ℚ)/528062500),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((1644840339:ℚ)/5000000000),((15743372422493877452461287489081788268608335893126179487296321:ℚ)/79969292675347995758056640625000000000000000000000000000000000),((1294169486828699667640153:ℚ)/2217984000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3603678043:ℚ)/5000000000),((36553523:ℚ)/50000000),((-407995799:ℚ)/528062500),((-9051034129:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1614229867:ℚ)/5000000000),((58826557226813637005315348850452057421308061410572873:ℚ)/298794614278416061401367187500000000000000000000000000),((269688385461870160144001571:ℚ)/462080000000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3611126291:ℚ)/5000000000),((91756017:ℚ)/125000000),((-1024828221:ℚ)/1323125000),((-9073378873:ℚ)/13290625000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((633219679:ℚ)/2000000000),((12983068720396564066481858430501630881528216610154489087197:ℚ)/65465639937425429153442382812500000000000000000000000000000),((269859000133625367289689299:ℚ)/462080000000000000000000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((1450408973:ℚ)/2000000000),((7370257323:ℚ)/10000000000),((-82373345199:ℚ)/106325000000),((-3647226919:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((607534397:ℚ)/2000000000),((737635481126936485059501347811734181448584447602093560108407:ℚ)/3719171645117901611328125000000000000000000000000000000000000),((43199704823021716297107091:ℚ)/73932800000000000000000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((728183621:ℚ)/1000000000),((7400032499:ℚ)/10000000000),((-82760422487:ℚ)/106800000000),((-1832550863:ℚ)/2681875000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((181484883:ℚ)/625000000),((36205561024502451749913726009093418976640356963099025760353133:ℚ)/182536443448439062500000000000000000000000000000000000000000000),((10805481945141814033271139:ℚ)/18483200000000000000000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((7311626631:ℚ)/10000000000),((3714903449:ℚ)/5000000000),((-41573744837:ℚ)/53637500000),((-18414879893:ℚ)/26937500000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1381779261:ℚ)/5000000000),((34705196515229066771049950768137564053516651758211125293589:ℚ)/174960569491614472866058349609375000000000000000000000000000),((3243308167800132789437182657:ℚ)/5544960000000000000000000000)⟩
theorem valid15 : Valid source23 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source23 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((367070807:ℚ)/500000000),((117021147:ℚ)/156250000),((-1311274911:ℚ)/1683593750),((-925212421:ℚ)/1358750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2616062043:ℚ)/10000000000),((886116034618892285144334970761472305419916369982934610981:ℚ)/4405153366405470296740531921386718750000000000000000000000),((2706159017394134706492171:ℚ)/4620800000000000000000000)⟩
theorem valid16 : Valid source23 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((740099247:ℚ)/1000000000),((475527347:ℚ)/625000000),((-5341855511:ℚ)/6793750000),((-1868297741:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2293481353:ℚ)/10000000000),((483707871327905586407047293306569799933229923005790017183:ℚ)/2341094792526525259017944335937500000000000000000000000000),((32548597352876114747971633:ℚ)/55449600000000000000000000)⟩
theorem valid17 : Valid source23 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((3760067351:ℚ)/5000000000),((784657241:ℚ)/1000000000),((-8856544133:ℚ)/11060000000),((-9520202053:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1451003013:ℚ)/10000000000),((55522479271584492806300276011097195325755808254931233341:ℚ)/255782470212500000000000000000000000000000000000000000000),((270979759811105566304970379:ℚ)/462080000000000000000000000)⟩
theorem valid18 : Valid source23 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((3879189949:ℚ)/5000000000),((8798738309:ℚ)/10000000000),((-100943598017:ℚ)/114400000000),((-9877569847:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1187094864865860276373560484539668925613982334936847469731:ℚ)/4306559400000000000000000000000000000000000000000000000000),((15002999:ℚ)/25600000)⟩
theorem valid19 : Valid source23 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((348436879:ℚ)/400000000),((10701832583:ℚ)/10000000000),((-125683823579:ℚ)/129600000000),((-904510637:ℚ)/1600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((71143117019233877769043493379630226605409130481845825947:ℚ)/212576400000000000000000000000000000000000000000000000000),((15002999:ℚ)/25600000)⟩
theorem valid20 : Valid source23 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10614553067:ℚ)/10000000000),((725273069:ℚ)/500000000),(-1:ℚ),((-28323659201:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2006392987039063277090693:ℚ)/5290000000000000000000000),((15002999:ℚ)/25600000)⟩
theorem valid21 : Valid source23 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source23 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source23 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((8411:ℚ)/12800) ((8449:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8449:ℚ)/12800) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((8449:ℚ)/12800) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((8449:ℚ)/12800) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source23 nn0 nn1 Qcell ((8449:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source23 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source23 nn0 nn1 Qcell ((8449:ℚ)/12800) ((431:ℚ)/640) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((143:ℚ)/200) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source23 nn0 nn1 Qcell ((8449:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC04
#check @N11Formalization.C450Source23GroupedC04.bound
#print axioms N11Formalization.C450Source23GroupedC04.valid0
#print axioms N11Formalization.C450Source23GroupedC04.valid1
#print axioms N11Formalization.C450Source23GroupedC04.valid2
#print axioms N11Formalization.C450Source23GroupedC04.valid3
#print axioms N11Formalization.C450Source23GroupedC04.valid4
#print axioms N11Formalization.C450Source23GroupedC04.valid5
#print axioms N11Formalization.C450Source23GroupedC04.valid6
#print axioms N11Formalization.C450Source23GroupedC04.valid7
#print axioms N11Formalization.C450Source23GroupedC04.valid8
#print axioms N11Formalization.C450Source23GroupedC04.valid9
#print axioms N11Formalization.C450Source23GroupedC04.valid10
#print axioms N11Formalization.C450Source23GroupedC04.valid11
#print axioms N11Formalization.C450Source23GroupedC04.valid12
#print axioms N11Formalization.C450Source23GroupedC04.valid13
#print axioms N11Formalization.C450Source23GroupedC04.valid14
#print axioms N11Formalization.C450Source23GroupedC04.valid15
#print axioms N11Formalization.C450Source23GroupedC04.valid16
#print axioms N11Formalization.C450Source23GroupedC04.valid17
#print axioms N11Formalization.C450Source23GroupedC04.valid18
#print axioms N11Formalization.C450Source23GroupedC04.valid19
#print axioms N11Formalization.C450Source23GroupedC04.valid20
#print axioms N11Formalization.C450Source23GroupedC04.valid21
#print axioms N11Formalization.C450Source23GroupedC04.bound
#print axioms N11Formalization.C450Source23GroupedC04.endpoint_checks
