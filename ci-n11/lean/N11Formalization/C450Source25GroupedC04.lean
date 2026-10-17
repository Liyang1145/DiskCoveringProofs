import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6860064827:ℚ)/10000000000),((282956713:ℚ)/400000000),((-3089637269:ℚ)/3968000000),((-5580064827:ℚ)/8425000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4449315951:ℚ)/10000000000),((12163048971668374707379586021538003440059140810977227833399:ℚ)/44346036440268800000000000000000000000000000000000000000000),((1823725124574526892362756333:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((6979380059:ℚ)/10000000000),((1783381223:ℚ)/2500000000),((-6501318633:ℚ)/8425000000),((-17098140177:ℚ)/25512500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2034659453:ℚ)/5000000000),((2596505054763624168975777952803817447055081380986218262187:ℚ)/9730961913439514160156250000000000000000000000000000000000),((1824649741318485525859288237:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((219969679:ℚ)/312500000),((3581663401:ℚ)/5000000000),((-39201624213:ℚ)/51025000000),((-359939358:ℚ)/533984375),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((120819321:ℚ)/312500000),((102098671501180626471266155310678156601349858867258065683174943:ℚ)/387887777762904516601562500000000000000000000000000000000000000),((1782323433779050776083857:ℚ)/2888000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((44180329:ℚ)/62500000),((1798281913:ℚ)/2500000000),((-19697664869:ℚ)/25631250000),((-108540987:ℚ)/160937500),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((1880390683:ℚ)/5000000000),((293940407493494397276850906642468804601516373791883471873791:ℚ)/1116513109392256164550781250000000000000000000000000000000000),((71330113596117365221757:ℚ)/115520000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1419734859:ℚ)/2000000000),((1444585491:ℚ)/2000000000),((-15835611383:ℚ)/20600000000),((-3491204577:ℚ)/5173750000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((3652455297:ℚ)/10000000000),((2464604799239601933442827586922238333152128302562250969753677:ℚ)/9359928501183500000000000000000000000000000000000000000000000),((219240052741849405971883111:ℚ)/354877440000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((712849471:ℚ)/1000000000),((7237826969:ℚ)/10000000000),((-79371750597:ℚ)/103475000000),((-1754548413:ℚ)/2592812500),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((1770487169:ℚ)/5000000000),((124678171586845987872042299168369910442470425557968734298447380543:ℚ)/476681725503742419042968750000000000000000000000000000000000000000),((18272176445182253594899957:ℚ)/29573120000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3571702229:ℚ)/5000000000),((3626363113:ℚ)/5000000000),((-39782720469:ℚ)/51856250000),((-2931702229:ℚ)/4331250000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((870989071:ℚ)/2500000000),((355474172099566855425018768895364165346792118524218138398763:ℚ)/1358936277074165725708007812500000000000000000000000000000000),((456922628915771142487142157:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-13:ℚ)/16),((-3:ℚ)/4),((3579156951:ℚ)/5000000000),((7267625229:ℚ)/10000000000),((-79759127977:ℚ)/103950000000),((-8817470853:ℚ)/13023437500),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((3426029931:ℚ)/10000000000),((1275910221666030543573410024012527334929155741965809149876039883:ℚ)/4877134209013216992187500000000000000000000000000000000000000000),((1371122131556089590470401231:ℚ)/2217984000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1434644609:ℚ)/2000000000),((7282523979:ℚ)/10000000000),((-79952811727:ℚ)/104187500000),((-3535933827:ℚ)/5221250000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((21044677:ℚ)/62500000),((8066722331057131432001662070474462790533764344081512622910946837:ℚ)/30831583325455027389526367187500000000000000000000000000000000000),((3849757102701428809966423:ℚ)/6225920000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((449258243:ℚ)/625000000),((3648711239:ℚ)/5000000000),((-40073246107:ℚ)/52212500000),((-738516486:ℚ)/1090234375),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((82681509:ℚ)/250000000),((453325071047685764396713749354650794543283922438182326500701473:ℚ)/1732459791152126077270507812500000000000000000000000000000000000),((7144944769146276003158573:ℚ)/11552000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3601520217:ℚ)/5000000000),((914040091:ℚ)/1250000000),((-3347507061:ℚ)/4360937500),((-8884560651:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((129852411:ℚ)/400000000),((37316584618178551186346134138989843531191088810669338901699:ℚ)/142597066038656657934188842773437500000000000000000000000000),((1372182415130845534034318959:ℚ)/2217984000000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((1443589737:ℚ)/2000000000),((732721873:ℚ)/1000000000),((-8053384349:ℚ)/10490000000),((-3562769211:ℚ)/5256875000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((1592118497:ℚ)/5000000000),((133578697583282632403080898664953138566943438817068861311205839:ℚ)/510389519513585806250000000000000000000000000000000000000000000),((219605604197812780809807439:ℚ)/354877440000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((3616428321:ℚ)/5000000000),((7342116487:ℚ)/10000000000),((-80727514331:ℚ)/105137500000),((-2976428321:ℚ)/4390625000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((195060839:ℚ)/625000000),((1501221066335912069610280541801431210576259445404693052795801:ℚ)/5735424868928014038085937500000000000000000000000000000000000),((1372887229113611266919735071:ℚ)/2217984000000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1811941077:ℚ)/2500000000),((7371911269:ℚ)/10000000000),((-81114846497:ℚ)/105375000000),((-61312647:ℚ)/90625000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3056445571:ℚ)/10000000000),((180088590302935512910122461807533771030738189218449120711147:ℚ)/683354827185058593750000000000000000000000000000000000000000),((343446640194744804361048999:ℚ)/554496000000000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3638789387:ℚ)/5000000000),((7401705087:ℚ)/10000000000),((-81502166131:ℚ)/105850000000),((-8996368161:ℚ)/13290625000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1461630081:ℚ)/5000000000),((35338680807357060582245642533601002311842781564716994449294675289:ℚ)/134073630591847278906250000000000000000000000000000000000000000000),((458162969335130796225864013:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((7307392099:ℚ)/10000000000),((3715748977:ℚ)/5000000000),((-40944736701:ℚ)/53162500000),((-6027392099:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((2783905997:ℚ)/10000000000),((490216924580337356310956169123016055793927298832596697603911:ℚ)/1859585822558950805664062500000000000000000000000000000000000),((1833586164400237547803670877:ℚ)/2957312000000000000000000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((7337204297:ℚ)/10000000000),((7491080887:ℚ)/10000000000),((-82664051531:ℚ)/106800000000),((-18171612891:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((329675587:ℚ)/1250000000),((1475722146015063669793901591981298912916881014660161597443041:ℚ)/5524695551629687500000000000000000000000000000000000000000000),((1835978201654502971038101893:ℚ)/2957312000000000000000000000)⟩
theorem valid16 : Valid source25 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((59174603:ℚ)/80000000),((7550660167:ℚ)/10000000000),((-83438582171:ℚ)/107750000000),((-146803809:ℚ)/217400000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2317475921:ℚ)/10000000000),((2467990635723920236943584569459458670755178845564686698391205369:ℚ)/9238276192663964843750000000000000000000000000000000000000000000),((117621492019792188944333:ℚ)/189267968000000000000000)⟩
theorem valid17 : Valid source25 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source25 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((59651537:ℚ)/80000000),((3834904073:ℚ)/5000000000),((-42493752949:ℚ)/54350000000),((-21176373:ℚ)/31600000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1946738937:ℚ)/10000000000),((26801610621812108362741159209641475198886146753540757207711:ℚ)/97848206838659667968750000000000000000000000000000000000000),((117707719446285851832213:ℚ)/189267968000000000000000)⟩
theorem valid18 : Valid source25 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((1893915773:ℚ)/2500000000),((7722719:ℚ)/9765625),((-24577242:ℚ)/30859375),((-4721747319:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((200122939:ℚ)/2500000000),((663052550212996400107670036088033527606798328790247:ℚ)/2311320146918296813964843750000000000000000000000000),((114813519722986067319541533:ℚ)/184832000000000000000000000)⟩
theorem valid19 : Valid source25 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((781405783:ℚ)/1000000000),((8860643541:ℚ)/10000000000),((-100468366033:ℚ)/114400000000),((-653405783:ℚ)/1080000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((204414007581099827312534148777772910310468129985854858969929:ℚ)/568465840800000000000000000000000000000000000000000000000000),((635931363:ℚ)/1024000000)⟩
theorem valid20 : Valid source25 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((8767109629:ℚ)/10000000000),((9812679561:ℚ)/10000000000),((-112844834293:ℚ)/129600000000),((-22461328887:ℚ)/36200000000),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),(0:ℚ),((9684745164037311491257096810098841639027419154131954135371767:ℚ)/27856861761600000000000000000000000000000000000000000000000000),((635931363:ℚ)/1024000000)⟩
theorem valid21 : Valid source25 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((9719518257:ℚ)/10000000000),((10764327721:ℚ)/10000000000),((-125216260373:ℚ)/144800000000),((-25318554771:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((6429948224106701270383446083509884003409515324891838733967:ℚ)/18975171200000000000000000000000000000000000000000000000000),((635931363:ℚ)/1024000000)⟩
theorem valid22 : Valid source25 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source25 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨(1:ℚ),((119:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((426858713:ℚ)/400000000),((6333416527:ℚ)/5000000000),((-74974414851:ℚ)/80000000000),((-1126976139:ℚ)/1904000000),((4638999999:ℚ)/5000000000),((4772478993:ℚ)/5000000000),((1911621469:ℚ)/5000000000),(0:ℚ),((655493556861340890745130867360537488514781051677802528644487:ℚ)/1618400000000000000000000000000000000000000000000000000000000),((635931363:ℚ)/1024000000)⟩
theorem valid23 : Valid source25 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((119:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((119:ℚ)/100),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((12574430989:ℚ)/10000000000),((14568647507:ℚ)/10000000000),((-24953202513:ℚ)/27200000000),((-11294430989:ℚ)/18400000000),((9544957981:ℚ)/10000000000),(1:ℚ),((189269891:ℚ)/625000000),(0:ℚ),((1028967441588943766183816468929092249209:ℚ)/2661352448000000000000000000000000000000),((635931363:ℚ)/1024000000)⟩
theorem valid24 : Valid source25 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source25 nn0 nn1 Qcell ((119:ℚ)/100) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet24 valid24
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4101:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((8297:ℚ)/12800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((8297:ℚ)/12800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((8297:ℚ)/12800) ((4177:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((8373:ℚ)/12800) ((8411:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source25 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8411:ℚ)/12800) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source25 nn0 nn1 Qcell ((8297:ℚ)/12800) ((8411:ℚ)/12800) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((8411:ℚ)/12800) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source25 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source25 nn0 nn1 Qcell ((8411:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source25 nn0 nn1 Qcell ((8411:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf18 node19_21
private theorem node21_23 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join node21_23 node23_25
private theorem node18_25 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node18_21 node21_25
private theorem node12_25 :
    CellBound source25 nn0 nn1 Qcell ((8411:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node12_18 node18_25
private theorem node0_25 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_25
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_25
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24]
theorem packet_count : packets.length = 25 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC04
#check @N11Formalization.C450Source25GroupedC04.bound
#print axioms N11Formalization.C450Source25GroupedC04.valid0
#print axioms N11Formalization.C450Source25GroupedC04.valid1
#print axioms N11Formalization.C450Source25GroupedC04.valid2
#print axioms N11Formalization.C450Source25GroupedC04.valid3
#print axioms N11Formalization.C450Source25GroupedC04.valid4
#print axioms N11Formalization.C450Source25GroupedC04.valid5
#print axioms N11Formalization.C450Source25GroupedC04.valid6
#print axioms N11Formalization.C450Source25GroupedC04.valid7
#print axioms N11Formalization.C450Source25GroupedC04.valid8
#print axioms N11Formalization.C450Source25GroupedC04.valid9
#print axioms N11Formalization.C450Source25GroupedC04.valid10
#print axioms N11Formalization.C450Source25GroupedC04.valid11
#print axioms N11Formalization.C450Source25GroupedC04.valid12
#print axioms N11Formalization.C450Source25GroupedC04.valid13
#print axioms N11Formalization.C450Source25GroupedC04.valid14
#print axioms N11Formalization.C450Source25GroupedC04.valid15
#print axioms N11Formalization.C450Source25GroupedC04.valid16
#print axioms N11Formalization.C450Source25GroupedC04.valid17
#print axioms N11Formalization.C450Source25GroupedC04.valid18
#print axioms N11Formalization.C450Source25GroupedC04.valid19
#print axioms N11Formalization.C450Source25GroupedC04.valid20
#print axioms N11Formalization.C450Source25GroupedC04.valid21
#print axioms N11Formalization.C450Source25GroupedC04.valid22
#print axioms N11Formalization.C450Source25GroupedC04.valid23
#print axioms N11Formalization.C450Source25GroupedC04.valid24
#print axioms N11Formalization.C450Source25GroupedC04.bound
#print axioms N11Formalization.C450Source25GroupedC04.endpoint_checks
