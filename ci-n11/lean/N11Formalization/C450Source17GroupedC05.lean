import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((1649292767:ℚ)/2500000000),((6903566477:ℚ)/10000000000),((-18310699431:ℚ)/24800000000),((-15582220437:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1298844099:ℚ)/2500000000),((34589866918198054037735615456778029042042004106405011401527:ℚ)/505684350400000000000000000000000000000000000000000000000000),((5452866411339156794181051:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3417618963:ℚ)/5000000000),((217595909:ℚ)/312500000),((-577787727:ℚ)/804687500),((-32473808593:ℚ)/51975000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2262310893:ℚ)/5000000000),((10000431320048327656011782568039458621771325329168994409:ℚ)/159951415969803929328918457031250000000000000000000000000),((21805073791236607267146771:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6894748143:ℚ)/10000000000),((351128469:ℚ)/500000000),((-311128469:ℚ)/433125000),((-65602229573:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((434207553:ℚ)/1000000000),((8740198149466943124217793734524794210857323157547178791:ℚ)/139704616750853347778320312500000000000000000000000000000),((87242200535292909745978491:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3477127951:ℚ)/5000000000),((7082067417:ℚ)/10000000000),((-18846202251:ℚ)/26225000000),((-33128407461:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((16218943:ℚ)/39062500),((7469511410498723862931745770250686775658029651410251026111:ℚ)/119321133492822265625000000000000000000000000000000000000000),((21815990974732772484025659:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((701376127:ℚ)/1000000000),((888976951:ℚ)/1250000000),((-2366930853:ℚ)/3307812500),((-6691137397:ℚ)/10632500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1976730527:ℚ)/5000000000),((126226590736370977784845094231165838470133801897806407986849:ℚ)/2045801248044544661045074462890625000000000000000000000000000),((45929730299434993847769:ℚ)/121600000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((3521756539:ℚ)/5000000000),((7141563257:ℚ)/10000000000),((-19024689771:ℚ)/26581250000),((-11206440643:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((962635763:ℚ)/2500000000),((7173738800090344165064886405846235930248977354311954211663:ℚ)/116224113909934425354003906250000000000000000000000000000000),((21819311345209465945832739:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((884158039:ℚ)/1250000000),((7171310373:ℚ)/10000000000),((-71587757:ℚ)/100000000),((-8445738429:ℚ)/13409375000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3744944487:ℚ)/10000000000),((55512924587724371907139479980013840309402427853814989:ℚ)/899056689453125000000000000000000000000000000000000000),((1363874495470906307660739:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((7103014979:ℚ)/10000000000),((7201056961:ℚ)/10000000000),((-19203170883:ℚ)/26818750000),((-67893164769:ℚ)/107750000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1818215663:ℚ)/5000000000),((10806892174967205226948887014835329554437958139181516681969:ℚ)/174960569491614472866058349609375000000000000000000000000000),((87298654560097105595036019:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((222898909:ℚ)/312500000),((7230803029:ℚ)/10000000000),((-19292409087:ℚ)/26937500000),((-710629333:ℚ)/1127343750),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3524733851:ℚ)/10000000000),((491184625325841801346224070303642975900955753290587166154879:ℚ)/7949403903329801559448242187500000000000000000000000000000000),((170525988154900665922533:ℚ)/451250000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3581257323:ℚ)/5000000000),((907568573:ℚ)/1250000000),((-807568573:ℚ)/1127343750),((-34273830553:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((136381543:ℚ)/400000000),((23566821025988330412018781085521807195663236683922984487:ℚ)/381281033669149875640869140625000000000000000000000000000),((21829980460063662399873411:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7192263659:ℚ)/10000000000),((56955419:ℚ)/78125000),((-304232514:ℚ)/424609375),((-68874900249:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((1645238799:ℚ)/5000000000),((102576990886673094428001922115811103871151280299394265427:ℚ)/1659023156900403648614883422851562500000000000000000000000),((87330502279025764386408579:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((902751517:ℚ)/1250000000),((366001909:ℚ)/500000000),((-978005727:ℚ)/1364687500),((-2883422229:ℚ)/4568750000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((395889299:ℚ)/1250000000),((1526129387012161327288771361215669252523890487743530833:ℚ)/24674932283651852607727050781250000000000000000000000000),((1364703863366625213996051:ℚ)/3610000000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((7251760083:ℚ)/10000000000),((3674891117:ℚ)/5000000000),((-3274891117:ℚ)/4568750000),((-69529360913:ℚ)/110125000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((607784893:ℚ)/2000000000),((3577696818702653607052842954722840539376208602978488449021:ℚ)/57827448443689537048339843750000000000000000000000000000000),((87351556773593832800066451:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7281507507:ℚ)/10000000000),((7379525801:ℚ)/10000000000),((-19738577403:ℚ)/27531250000),((-69856582577:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((726317087:ℚ)/2500000000),((308544644302073561716067776737102248132157535280417948984581:ℚ)/4985607480010247230529785156250000000000000000000000000000000),((87362030837762739242967891:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3655627207:ℚ)/5000000000),((14878023:ℚ)/20000000),((-39834069:ℚ)/55300000),((-35091899277:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((69133823:ℚ)/250000000),((1474585833009406334499752737343687269266389070361699:ℚ)/23485863557396679687500000000000000000000000000000000),((21847890985449269541650091:ℚ)/57760000000000000000000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((7370746707:ℚ)/10000000000),((7498495323:ℚ)/10000000000),((-20095485969:ℚ)/27887500000),((-70838213777:ℚ)/112500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((246242939:ℚ)/1000000000),((27772521363594902524742336539660267811220226225881607:ℚ)/442162682676315307617187500000000000000000000000000000),((87412334237047172452307091:ℚ)/231040000000000000000000000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((7430237013:ℚ)/10000000000),((7617457533:ℚ)/10000000000),((-6817457533:ℚ)/9375000000),((-71492607143:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((211758791:ℚ)/1000000000),((308968798476877586948717770685254935352454819214652452959:ℚ)/4786777496337890625000000000000000000000000000000000000000),((87459940975514988711187971:ℚ)/231040000000000000000000000)⟩
theorem valid16 : Valid source17 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((7549211863:ℚ)/10000000000),((4046620057:ℚ)/5000000000),((-10939860171:ℚ)/14300000000),((-72801330493:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((578364327:ℚ)/5000000000),((2529789943458996437785341082039657100886937577521322803683:ℚ)/34003044521875000000000000000000000000000000000000000000000),((87424402570336196520535371:ℚ)/231040000000000000000000000)⟩
theorem valid17 : Valid source17 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((1003130131:ℚ)/1250000000),((8568930711:ℚ)/10000000000),((-23306792133:ℚ)/30500000000),((-3251477147:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4758464753288051588844768682316572091172746246740470457949:ℚ)/64636386328125000000000000000000000000000000000000000000000),((6053259:ℚ)/16000000)⟩
theorem valid18 : Valid source17 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((4250386379:ℚ)/5000000000),((2094207197:ℚ)/2000000000),((-1934207197:ℚ)/2160000000),((-41634250169:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((628820478778341660179811778385067460183473896931247:ℚ)/5904900000000000000000000000000000000000000000000000),((6053259:ℚ)/16000000)⟩
theorem valid19 : Valid source17 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10403003301:ℚ)/10000000000),((14273505721:ℚ)/10000000000),(-1:ℚ),((-104193036311:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((855268160414969515308214043:ℚ)/6094080000000000000000000000),((6053259:ℚ)/16000000)⟩
theorem valid20 : Valid source17 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source17 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source17 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source17 nn0 nn1 Qcell ((4253:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source17 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC05
#check @N11Formalization.C450Source17GroupedC05.bound
#print axioms N11Formalization.C450Source17GroupedC05.valid0
#print axioms N11Formalization.C450Source17GroupedC05.valid1
#print axioms N11Formalization.C450Source17GroupedC05.valid2
#print axioms N11Formalization.C450Source17GroupedC05.valid3
#print axioms N11Formalization.C450Source17GroupedC05.valid4
#print axioms N11Formalization.C450Source17GroupedC05.valid5
#print axioms N11Formalization.C450Source17GroupedC05.valid6
#print axioms N11Formalization.C450Source17GroupedC05.valid7
#print axioms N11Formalization.C450Source17GroupedC05.valid8
#print axioms N11Formalization.C450Source17GroupedC05.valid9
#print axioms N11Formalization.C450Source17GroupedC05.valid10
#print axioms N11Formalization.C450Source17GroupedC05.valid11
#print axioms N11Formalization.C450Source17GroupedC05.valid12
#print axioms N11Formalization.C450Source17GroupedC05.valid13
#print axioms N11Formalization.C450Source17GroupedC05.valid14
#print axioms N11Formalization.C450Source17GroupedC05.valid15
#print axioms N11Formalization.C450Source17GroupedC05.valid16
#print axioms N11Formalization.C450Source17GroupedC05.valid17
#print axioms N11Formalization.C450Source17GroupedC05.valid18
#print axioms N11Formalization.C450Source17GroupedC05.valid19
#print axioms N11Formalization.C450Source17GroupedC05.valid20
#print axioms N11Formalization.C450Source17GroupedC05.bound
#print axioms N11Formalization.C450Source17GroupedC05.endpoint_checks
