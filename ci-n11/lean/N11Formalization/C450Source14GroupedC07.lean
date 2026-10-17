import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6457285347:ℚ)/10000000000),((6749689197:ℚ)/10000000000),((-5981689197:ℚ)/9920000000),((-49795568123:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1110977449:ℚ)/2000000000),((3150405691122591705412151008918492244183269011640913906883:ℚ)/64727596851200000000000000000000000000000000000000000000000),((81087665041346187081785123:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((6695255343:ℚ)/10000000000),((6868671683:ℚ)/10000000000),((-6100671683:ℚ)/10300000000),((-51937298087:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4929204673:ℚ)/10000000000),((88022156506524627146539906633929601000468520898707315395717:ℚ)/1878809193010937500000000000000000000000000000000000000000000),((80793520000398703918759403:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((1362845507:ℚ)/2000000000),((6987645873:ℚ)/10000000000),((-6219645873:ℚ)/10490000000),((-10601609563:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4587451367:ℚ)/10000000000),((2008751289992913150652379614908913458239076075834281218469:ℚ)/42859564972167187500000000000000000000000000000000000000000),((3225850288818364115551203:ℚ)/14786560000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((34665959:ℚ)/50000000),((1409425999:ℚ)/2000000000),((-1255825999:ℚ)/2136000000),((-270393631:ℚ)/538750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((42202323:ℚ)/100000000),((6103124849481048303932328853576433648941535567912808763:ℚ)/132592693239112500000000000000000000000000000000000000000),((2012471672094686278107:ℚ)/9241600000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1748167773:ℚ)/2500000000),((1421322441:ℚ)/2000000000),((-1267722441:ℚ)/2155000000),((-13653509957:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2012452381:ℚ)/5000000000),((3403077175999139117591843110892341468868624541048213048711:ℚ)/73906209541311718750000000000000000000000000000000000000000),((5026570232900613841945763:ℚ)/23104000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((1410429711:ℚ)/2000000000),((223011019:ℚ)/312500000),((-199011019:ℚ)/339687500),((-11029867399:ℚ)/21835000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3820178503:ℚ)/10000000000),((13326962058561695828889451288735216609950882452097015129:ℚ)/291988075614471042156219482421875000000000000000000000000),((3214053940019202623292587:ℚ)/14786560000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7081886617:ℚ)/10000000000),((895761569:ℚ)/1250000000),((-799761569:ℚ)/1364687500),((-55416979553:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((1856903339:ℚ)/5000000000),((17095764729255564743266448955827205541747202968162714319:ℚ)/374478384069539880752563476562500000000000000000000000000),((80314448842477180541144283:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((7111624239:ℚ)/10000000000),((3597916021:ℚ)/5000000000),((-3213916021:ℚ)/5482500000),((-55684618151:ℚ)/110125000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3604448231:ℚ)/10000000000),((9125626749846218062217836029671416691071588243875775321891:ℚ)/199851661821391040039062500000000000000000000000000000000000),((80277541147102988886775787:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((1785340357:ℚ)/2500000000),((1806392771:ℚ)/2500000000),((-1614392771:ℚ)/2753125000),((-13988063213:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3491822033:ℚ)/10000000000),((42693811188682425131016059866852315747358150483485751401:ℚ)/934801402501921355724334716796875000000000000000000000000),((5015039087877979857210003:ℚ)/23104000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7171098189:ℚ)/10000000000),((1813827421:ℚ)/2500000000),((-1621827421:ℚ)/2765000000),((-56219883701:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((135024019:ℚ)/400000000),((9928200168520168531926204220056941757013569610130671856537:ℚ)/217338569724080273437500000000000000000000000000000000000000),((80203701613477012506113987:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((225026079:ℚ)/312500000),((910630981:ℚ)/1250000000),((-814630981:ℚ)/1388437500),((-1765234711:ℚ)/3485937500),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3255397943:ℚ)/10000000000),((237770303542699958088256489986045637788601630084389648751:ℚ)/5204010690085122907161712646484375000000000000000000000000),((78287861096004745588427:ℚ)/361000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7230570449:ℚ)/10000000000),((3657392791:ℚ)/5000000000),((-3273392791:ℚ)/5577500000),((-56755134041:ℚ)/112025000000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((1565377681:ℚ)/5000000000),((39802594578471939552875783259934861427011436953882729215881:ℚ)/870980904065008402343750000000000000000000000000000000000000),((80129829847938972725050347:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((7260305959:ℚ)/10000000000),((734452289:ℚ)/1000000000),((-657652289:ℚ)/1120250000),((-57022753631:ℚ)/112500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3001118961:ℚ)/10000000000),((21178850858236212107214099317859553799551761998671:ℚ)/463360147344017028808593750000000000000000000000000),((80092881862030387495318107:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7290041063:ℚ)/10000000000),((7403996251:ℚ)/10000000000),((-6635996251:ℚ)/11250000000),((-57290369567:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((573162101:ℚ)/2000000000),((5281930498715730445699217818247134564488438677234252339261:ℚ)/114537206085205078125000000000000000000000000000000000000000),((80055925798724027357140443:ℚ)/369664000000000000000000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((918688759:ℚ)/1250000000),((298538719:ℚ)/400000000),((-267818719:ℚ)/453800000),((-7228198831:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((643640631:ℚ)/2500000000),((550931654160928673635466476939532752212859024016556649:ℚ)/11943883727397050000000000000000000000000000000000000000),((1249718584651505564726907:ℚ)/5776000000000000000000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1481795503:ℚ)/2000000000),((473900417:ℚ)/625000000),((-425900417:ℚ)/715000000),((-11672159527:ℚ)/23260000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((449359899:ℚ)/2000000000),((13178562738179212656972881877787063264109937156402265437:ℚ)/280908504103906250000000000000000000000000000000000000000),((8854074311259133953843:ℚ)/40960000000000000000000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((3763953931:ℚ)/5000000000),((962667411:ℚ)/1250000000),((-866667411:ℚ)/1453750000),((-29715585379:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1378465993:ℚ)/10000000000),((8740547467638100447522782939582621177939262178718922461:ℚ)/186303777842172241210937500000000000000000000000000000000),((19939996455531945478050867:ℚ)/92416000000000000000000000)⟩
theorem valid16 : Valid source14 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((7646832397:ℚ)/10000000000),((3969593709:ℚ)/5000000000),((-1195197903:ℚ)/1970000000),((-60501491573:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((8602946877740268166165035568973501386780787770205548233:ℚ)/177802705831250000000000000000000000000000000000000000000),((27586629:ℚ)/128000000)⟩
theorem valid17 : Valid source14 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((63077321:ℚ)/80000000),((1051852789:ℚ)/1250000000),((-955852789:ℚ)/1525000000),((-501135889:ℚ)/1036800000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2476345688416007303335192621050074974514293316354140577:ℚ)/48477289746093750000000000000000000000000000000000000000),((27586629:ℚ)/128000000)⟩
theorem valid18 : Valid source14 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4180135967:ℚ)/5000000000),((322398683:ℚ)/312500000),((-298398683:ℚ)/405000000),((-33461223703:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((81611545647084227983222701525820994646625915995119:ℚ)/1245564843750000000000000000000000000000000000000000),((27586629:ℚ)/128000000)⟩
theorem valid19 : Valid source14 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((5131060947:ℚ)/5000000000),((7059514301:ℚ)/5000000000),((-6675514301:ℚ)/8000000000),((-42019548523:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((102040578366644030107054814902685799791559988959231777313:ℚ)/1269600000000000000000000000000000000000000000000000000000),((27586629:ℚ)/128000000)⟩
theorem valid20 : Valid source14 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4443:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4443:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((4443:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source14 nn0 nn1 Qcell ((4481:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC07
#check @N11Formalization.C450Source14GroupedC07.bound
#print axioms N11Formalization.C450Source14GroupedC07.valid0
#print axioms N11Formalization.C450Source14GroupedC07.valid1
#print axioms N11Formalization.C450Source14GroupedC07.valid2
#print axioms N11Formalization.C450Source14GroupedC07.valid3
#print axioms N11Formalization.C450Source14GroupedC07.valid4
#print axioms N11Formalization.C450Source14GroupedC07.valid5
#print axioms N11Formalization.C450Source14GroupedC07.valid6
#print axioms N11Formalization.C450Source14GroupedC07.valid7
#print axioms N11Formalization.C450Source14GroupedC07.valid8
#print axioms N11Formalization.C450Source14GroupedC07.valid9
#print axioms N11Formalization.C450Source14GroupedC07.valid10
#print axioms N11Formalization.C450Source14GroupedC07.valid11
#print axioms N11Formalization.C450Source14GroupedC07.valid12
#print axioms N11Formalization.C450Source14GroupedC07.valid13
#print axioms N11Formalization.C450Source14GroupedC07.valid14
#print axioms N11Formalization.C450Source14GroupedC07.valid15
#print axioms N11Formalization.C450Source14GroupedC07.valid16
#print axioms N11Formalization.C450Source14GroupedC07.valid17
#print axioms N11Formalization.C450Source14GroupedC07.valid18
#print axioms N11Formalization.C450Source14GroupedC07.valid19
#print axioms N11Formalization.C450Source14GroupedC07.valid20
#print axioms N11Formalization.C450Source14GroupedC07.bound
#print axioms N11Formalization.C450Source14GroupedC07.endpoint_checks
