import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6299564147:ℚ)/10000000000),((6571065719:ℚ)/10000000000),((-41517460033:ℚ)/99200000000),((-16338692441:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((47494061:ℚ)/80000000),((1779770173640098156064036499491504874767637085149558970141:ℚ)/79393446093750000000000000000000000000000000000000000000000),((1216506631440662953738839163:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6537264859:ℚ)/10000000000),((6808794871:ℚ)/10000000000),((-43181564097:ℚ)/103000000000),((-17051794577:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5352004219:ℚ)/10000000000),((547270629982126943708662422526412348380836317084873804143:ℚ)/24506484862500000000000000000000000000000000000000000000000),((1207839362831972800175604603:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((846868909:ℚ)/1250000000),((6927653431:ℚ)/10000000000),((-14671191339:ℚ)/35600000000),((-2220606727:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4702810777:ℚ)/10000000000),((3796353255566619447506192305923405479503191035179281759:ℚ)/174420974375915527343750000000000000000000000000000000000),((1197391270335375189468397563:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1378757917:ℚ)/2000000000),((3493540649:ℚ)/5000000000),((-22214784543:ℚ)/54350000000),((-3624273751:ℚ)/10965000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2172536313:ℚ)/5000000000),((16046830575411671475066745677560010945363577139348008643:ℚ)/746370083525976562500000000000000000000000000000000000000),((298044912162042732838017083:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((6953207593:ℚ)/10000000000),((220203383:ℚ)/312500000),((-467141227:ℚ)/1142187500),((-18299622779:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2077733797:ℚ)/5000000000),((778387542225465382426445366657332025277827020692596737691:ℚ)/36217133082128906250000000000000000000000000000000000000000),((1162165849107909096360287:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7012624861:ℚ)/10000000000),((7105934327:ℚ)/10000000000),((-6465934327:ℚ)/15800000000),((-18477874583:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1978670897:ℚ)/5000000000),((115037132139654828672125561634209652500329943162906107049:ℚ)/5354338982476806640625000000000000000000000000000000000000),((1187944162557548362659427707:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((110500647:ℚ)/156250000),((3567823519:ℚ)/5000000000),((-22734764633:ℚ)/55775000000),((-583003882:ℚ)/1750390625),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((937335203:ℚ)/2500000000),((127782087090480693718553957292541136425444755416928183:ℚ)/5982387087526053190231323242187500000000000000000000000),((296337410906353679082380363:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7101749417:ℚ)/10000000000),((1433071907:ℚ)/2000000000),((-9135503349:ℚ)/22405000000),((-18745248251:ℚ)/56250000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3641110203:ℚ)/10000000000),((1247507588059207514693287021178401976419217365701770223281:ℚ)/58412235975265502929687500000000000000000000000000000000000),((47371916549847874879074467:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((7131457253:ℚ)/10000000000),((3597535911:ℚ)/5000000000),((-22942751377:ℚ)/56250000000),((-18834371759:ℚ)/56487500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1764857613:ℚ)/5000000000),((72167601469286737421007305772847348937613256913299107421:ℚ)/3379545789514160156250000000000000000000000000000000000000),((887436165988188286562656529:ℚ)/11089920000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3580582459:ℚ)/5000000000),((7224783901:ℚ)/10000000000),((-46093487307:ℚ)/112975000000),((-9461747377:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((426855713:ℚ)/1250000000),((34397356729733167041601675878411170921404753329962748351:ℚ)/1611001311693450927734375000000000000000000000000000000000),((1182200566226026074590094883:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((7190872413:ℚ)/10000000000),((290179831:ℚ)/400000000),((-1852058817:ℚ)/4538000000),((-2716088177:ℚ)/8137500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3296137867:ℚ)/10000000000),((54380267944013835045337453653992481211687941181959780127:ℚ)/2547218869299316406250000000000000000000000000000000000000),((1889847917483324647811963:ℚ)/23658496000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((3610289871:ℚ)/5000000000),((3642103723:ℚ)/5000000000),((-3322103723:ℚ)/8137500000),((-9550869613:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3173160413:ℚ)/10000000000),((677266340754359368708539304238049467691951018257945898293:ℚ)/31727645950000000000000000000000000000000000000000000000000),((295027841926190881351125107:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-7:ℚ)/16),((-3:ℚ)/8),((3625143453:ℚ)/5000000000),((7313918917:ℚ)/10000000000),((-46717432419:ℚ)/114400000000),((-9595430359:ℚ)/28718750000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((3045395577:ℚ)/10000000000),((1355510123576636295074607782114498648961823838644586716603:ℚ)/63508800279808044433593750000000000000000000000000000000000),((1179069824016075568542058387:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7279993907:ℚ)/10000000000),((7343630191:ℚ)/10000000000),((-46925411337:ℚ)/114875000000),((-19279981721:ℚ)/57675000000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2912212737:ℚ)/10000000000),((2755854899290112725151559181335886993865914503769167421:ℚ)/129133709782985687255859375000000000000000000000000000000),((1178030317266965012366377323:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((7309700747:ℚ)/10000000000),((3701526077:ℚ)/5000000000),((-7890227513:ℚ)/19225000000),((-19369102241:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2772830679:ℚ)/10000000000),((20271760346178310145744293946548935062623867127734438270697:ℚ)/945051583939843750000000000000000000000000000000000000000000),((294374519600314923172788707:ℚ)/3696640000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7369113953:ℚ)/10000000000),((3760946907:ℚ)/5000000000),((-24086628349:ℚ)/58150000000),((-19547341859:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2471227347:ℚ)/10000000000),((300962225040915527480002577886713555741883220391543942267:ℚ)/13893076248437500000000000000000000000000000000000000000000),((882343475255840029189473401:ℚ)/11089920000000000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((3743969261:ℚ)/5000000000),((96994607:ℚ)/125000000),((-207654083:ℚ)/492500000),((-9951907783:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1719378377:ℚ)/10000000000),((2312307235833889471341668813559838663932324424685365313929:ℚ)/104801383593750000000000000000000000000000000000000000000000),((3854127191677539:ℚ)/48640000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((1931395171:ℚ)/2500000000),((4117443639:ℚ)/5000000000),((-26582105473:ℚ)/61000000000),((-5154185513:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((12309379915399081397683080169329151395345024909596042263:ℚ)/540298350000000000000000000000000000000000000000000000000),((80737041:ℚ)/1024000000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((8200839979:ℚ)/10000000000),((2027171829:ℚ)/2000000000),((-13294202803:ℚ)/25920000000),((-22042519937:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2280762832875806379032531118774896204638572439277509564787:ℚ)/86400000000000000000000000000000000000000000000000000000000),((80737041:ℚ)/1024000000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((252540767:ℚ)/250000000),((3484249919:ℚ)/2500000000),((-23269749433:ℚ)/40000000000),((-693622301:ℚ)/2760000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2980181621595906930792388325762133360988573527892111:ℚ)/98552700000000000000000000000000000000000000000000000),((80737041:ℚ)/1024000000)⟩
theorem valid19 : Valid ninth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((919:ℚ)/1280) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC10
#check @N11Formalization.C450NinthGroupedC10.bound
#print axioms N11Formalization.C450NinthGroupedC10.valid0
#print axioms N11Formalization.C450NinthGroupedC10.valid1
#print axioms N11Formalization.C450NinthGroupedC10.valid2
#print axioms N11Formalization.C450NinthGroupedC10.valid3
#print axioms N11Formalization.C450NinthGroupedC10.valid4
#print axioms N11Formalization.C450NinthGroupedC10.valid5
#print axioms N11Formalization.C450NinthGroupedC10.valid6
#print axioms N11Formalization.C450NinthGroupedC10.valid7
#print axioms N11Formalization.C450NinthGroupedC10.valid8
#print axioms N11Formalization.C450NinthGroupedC10.valid9
#print axioms N11Formalization.C450NinthGroupedC10.valid10
#print axioms N11Formalization.C450NinthGroupedC10.valid11
#print axioms N11Formalization.C450NinthGroupedC10.valid12
#print axioms N11Formalization.C450NinthGroupedC10.valid13
#print axioms N11Formalization.C450NinthGroupedC10.valid14
#print axioms N11Formalization.C450NinthGroupedC10.valid15
#print axioms N11Formalization.C450NinthGroupedC10.valid16
#print axioms N11Formalization.C450NinthGroupedC10.valid17
#print axioms N11Formalization.C450NinthGroupedC10.valid18
#print axioms N11Formalization.C450NinthGroupedC10.valid19
#print axioms N11Formalization.C450NinthGroupedC10.bound
#print axioms N11Formalization.C450NinthGroupedC10.endpoint_checks
