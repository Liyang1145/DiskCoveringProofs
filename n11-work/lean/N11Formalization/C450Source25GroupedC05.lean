import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6796399433:ℚ)/10000000000),((1751691:ℚ)/2500000),((-4335073:ℚ)/6200000),((-59400393763:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4640144307:ℚ)/10000000000),((399079988918990407852439244020284112766463981823083:ℚ)/1522500335550000000000000000000000000000000000000000),((22810856247525119116850823:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3457915871:ℚ)/5000000000),((7066438257:ℚ)/10000000000),((-17519314771:ℚ)/25275000000),((-30357074581:ℚ)/51025000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((21378283:ℚ)/50000000),((22432205456343007976927031912791421886168896304845645245387:ℚ)/87578657220955627441406250000000000000000000000000000000000),((5692271892222711039288087:ℚ)/11552000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((6975538289:ℚ)/10000000000),((890763369:ℚ)/1250000000),((-2212290107:ℚ)/3189062500),((-61370921179:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((16328287:ℚ)/40000000),((1102150888446988665015063524774142391511583694077096598339:ℚ)/4301040723652315139770507812500000000000000000000000000000),((22756732878335988445568247:ℚ)/46208000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7035238669:ℚ)/10000000000),((7155939263:ℚ)/10000000000),((-17787817789:ℚ)/25750000000),((-62027625359:ℚ)/103475000000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((3879426079:ℚ)/10000000000),((4632016034481182683868446298202494429741652125775965939639799:ℚ)/18281110353874023437500000000000000000000000000000000000000000),((22735206328179946057420527:ℚ)/46208000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7065086601:ℚ)/10000000000),((5613883:ℚ)/7812500),((-223466384:ℚ)/323359375),((-6928439179:ℚ)/11550000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((471781311:ℚ)/1250000000),((296925175807117000970326425189880169663238990579903169:ℚ)/1171546711205649375915527343750000000000000000000000000),((22728803697298119919616007:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3547466527:ℚ)/5000000000),((7215599903:ℚ)/10000000000),((-17966799709:ℚ)/25987500000),((-31342131797:ℚ)/52212500000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3666212693:ℚ)/10000000000),((3675641409557803152084004257336070179751972207189171864036807:ℚ)/14498682638214743041992187500000000000000000000000000000000000),((5680584148142319109156503:ℚ)/11552000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((142495561:ℚ)/200000000),((7245428269:ℚ)/10000000000),((-18056284807:ℚ)/26106250000),((-1260251171:ℚ)/2098000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1777525577:ℚ)/5000000000),((7757531554616354386961233976801587601034723963895999999600597:ℚ)/30591761181292126846313476562500000000000000000000000000000000),((9086322006921347440647:ℚ)/18483200000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((7154621609:ℚ)/10000000000),((1818813839:ℚ)/2500000000),((-4536441517:ℚ)/6556250000),((-63340837699:ℚ)/105375000000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((3440462487:ℚ)/10000000000),((3174918498988530457161039849518536661993954679973494317287:ℚ)/12517041242846694946289062500000000000000000000000000000000),((22709208975959046048973767:ℚ)/46208000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7184463749:ℚ)/10000000000),((3652540591:ℚ)/5000000000),((-9117621773:ℚ)/13171875000),((-63669101239:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((664418291:ℚ)/2000000000),((1804521863737429908268398122619199133336694672114183740902727:ℚ)/7112495847791361808776855468750000000000000000000000000000000),((1194870972308767610100453:ℚ)/2432000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7214304491:ℚ)/10000000000),((7334905763:ℚ)/10000000000),((-18324717289:ℚ)/26462500000),((-63997349401:ℚ)/106325000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1599758813:ℚ)/5000000000),((531630863894784167500396977556831501888998025789836455082628851:ℚ)/2094900477997613732910156250000000000000000000000000000000000000),((22695823514026496004835167:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((7244143853:ℚ)/10000000000),((7364729117:ℚ)/10000000000),((-18414187351:ℚ)/26581250000),((-64325582383:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3072237337:ℚ)/10000000000),((531030780995046694842712205054760038727731565138903394520749:ℚ)/2092034050378819656372070312500000000000000000000000000000000),((22689034101435859787631663:ℚ)/46208000000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3636990927:ℚ)/5000000000),((7394551259:ℚ)/10000000000),((-18503653777:ℚ)/26700000000),((-32326900197:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((1469819307:ℚ)/5000000000),((413794008140243888341767940705414076129580328807955536932343:ℚ)/1629789673646777343750000000000000000000000000000000000000000),((5670545059877268108659703:ℚ)/11552000000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((456488657:ℚ)/625000000),((3712186103:ℚ)/5000000000),((-9296558309:ℚ)/13409375000),((-4061375227:ℚ)/6734375000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2800965507:ℚ)/10000000000),((2776975845060035365253278894304596162947931611680680658879:ℚ)/10935035593225904554128646850585937500000000000000000000000),((88575241924313714884443:ℚ)/180500000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((1466730769:ℚ)/2000000000),((3742005289:ℚ)/5000000000),((-9386015867:ℚ)/13468750000),((-13062038459:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((165954107:ℚ)/625000000),((4634019264689657794628247348072356065152847604961243803834777:ℚ)/18043508188796806335449218750000000000000000000000000000000000),((907087576661820360179127:ℚ)/1848320000000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7393320607:ℚ)/10000000000),((380163683:ℚ)/500000000),((-956491049:ℚ)/1358750000),((-65966526677:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((584367361:ℚ)/2500000000),((2808702977811377815266300532605578871118927264598254127:ℚ)/10702147622978401184082031250000000000000000000000000000),((22679869814963958352395543:ℚ)/46208000000000000000000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((3756319493:ℚ)/5000000000),((7841748383:ℚ)/10000000000),((-19845245149:ℚ)/27650000000),((-33639514423:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((151769299:ℚ)/1000000000),((56778629592038452986631414323159774965137223740030115328307:ℚ)/207823257047656250000000000000000000000000000000000000000000),((5653785716293833757855743:ℚ)/11552000000000000000000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((48445117:ℚ)/62500000),((4397536379:ℚ)/5000000000),((-11352609137:ℚ)/14300000000),((-436896287:ℚ)/810000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1023266876336549325562501338761711566093226060761589430037:ℚ)/3074634956250000000000000000000000000000000000000000000000),((7814091:ℚ)/16000000)⟩
theorem valid16 : Valid source25 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((1740980179:ℚ)/2000000000),((267495491:ℚ)/250000000),((-710486473:ℚ)/810000000),((-16078781969:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((81604208832217871245672904366538956350810862671807:ℚ)/207594140625000000000000000000000000000000000000000),((7814091:ℚ)/16000000)⟩
theorem valid17 : Valid source25 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((119:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((10610157851:ℚ)/10000000000),((50412187:ℚ)/40000000),((-136516561:ℚ)/160000000),((-101351736361:ℚ)/190400000000),((4638999999:ℚ)/5000000000),((4772478993:ℚ)/5000000000),((1911621469:ℚ)/5000000000),(0:ℚ),((4791594680369011685936588091872344975464691471263253:ℚ)/12947200000000000000000000000000000000000000000000000),((7814091:ℚ)/16000000)⟩
theorem valid18 : Valid source25 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((119:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((119:ℚ)/100),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((12513731257:ℚ)/10000000000),((7252691783:ℚ)/5000000000),((-19918075349:ℚ)/23800000000),((-122291043827:ℚ)/220800000000),((9544957981:ℚ)/10000000000),(1:ℚ),((189269891:ℚ)/625000000),(0:ℚ),((142448234844149250610719318761097954768751416512115721164599:ℚ)/401152099950000000000000000000000000000000000000000000000000),((7814091:ℚ)/16000000)⟩
theorem valid19 : Valid source25 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source25 nn0 nn1 Qcell ((119:ℚ)/100) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source25 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source25 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source25 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source25 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC05
#check @N11Formalization.C450Source25GroupedC05.bound
#print axioms N11Formalization.C450Source25GroupedC05.valid0
#print axioms N11Formalization.C450Source25GroupedC05.valid1
#print axioms N11Formalization.C450Source25GroupedC05.valid2
#print axioms N11Formalization.C450Source25GroupedC05.valid3
#print axioms N11Formalization.C450Source25GroupedC05.valid4
#print axioms N11Formalization.C450Source25GroupedC05.valid5
#print axioms N11Formalization.C450Source25GroupedC05.valid6
#print axioms N11Formalization.C450Source25GroupedC05.valid7
#print axioms N11Formalization.C450Source25GroupedC05.valid8
#print axioms N11Formalization.C450Source25GroupedC05.valid9
#print axioms N11Formalization.C450Source25GroupedC05.valid10
#print axioms N11Formalization.C450Source25GroupedC05.valid11
#print axioms N11Formalization.C450Source25GroupedC05.valid12
#print axioms N11Formalization.C450Source25GroupedC05.valid13
#print axioms N11Formalization.C450Source25GroupedC05.valid14
#print axioms N11Formalization.C450Source25GroupedC05.valid15
#print axioms N11Formalization.C450Source25GroupedC05.valid16
#print axioms N11Formalization.C450Source25GroupedC05.valid17
#print axioms N11Formalization.C450Source25GroupedC05.valid18
#print axioms N11Formalization.C450Source25GroupedC05.valid19
#print axioms N11Formalization.C450Source25GroupedC05.bound
#print axioms N11Formalization.C450Source25GroupedC05.endpoint_checks
