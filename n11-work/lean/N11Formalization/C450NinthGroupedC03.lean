import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((803168867:ℚ)/1250000000),((1343127131:ℚ)/2000000000),((-8953889917:ℚ)/9920000000),((-9801195271:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2817030631:ℚ)/5000000000),((5335923518622157296775082711835256639164371:ℚ)/202273740160000000000000000000000000000000000),((133224921512216675896024137:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((6662930247:ℚ)/10000000000),((854302429:ℚ)/1250000000),((-5700117003:ℚ)/6437500000),((-81498093211:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((501834981:ℚ)/1000000000),((87025114060759809386428707289785385009283758914212611057:ℚ)/3583544145604968070983886718750000000000000000000000000000),((52132483774965839787527097:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((6781717747:ℚ)/10000000000),((869150251:ℚ)/1250000000),((-5804051757:ℚ)/6556250000),((-83042330711:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4683124593:ℚ)/10000000000),((3044487337511562672487107040026020019164186305168979302099:ℚ)/125565131754396057128906250000000000000000000000000000000000),((52224133224758294469381417:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((6900503913:ℚ)/10000000000),((219143527:ℚ)/312500000),((-488001563:ℚ)/556250000),((-84586550869:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((172961529:ℚ)/400000000),((13965908119826048156532016425007673883909903230997928393:ℚ)/599467833293151855468750000000000000000000000000000000000),((3266875903288752382176993:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((6959896517:ℚ)/10000000000),((7071983443:ℚ)/10000000000),((-47263884101:ℚ)/53875000000),((-85358654721:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2066805771:ℚ)/5000000000),((26895502642213066807536328841708991941956549852142836582960853:ℚ)/1154784524082995605468750000000000000000000000000000000000000000),((3348219734841526685003471833:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7019288813:ℚ)/10000000000),((7101678631:ℚ)/10000000000),((-47471750417:ℚ)/54350000000),((-86130754569:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((1967266627:ℚ)/5000000000),((81937352516398933349145644522833421546241912004720839817513147:ℚ)/3587949473150620166015625000000000000000000000000000000000000000),((3349690044119473762576855137:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((440561553:ℚ)/625000000),((7131373753:ℚ)/10000000000),((-47679616271:ℚ)/54587500000),((-5407300189:ℚ)/6853125000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3831329457:ℚ)/10000000000),((597061061705378849411628141647139199284303970544408609753869:ℚ)/26145399905946057128906250000000000000000000000000000000000000),((3351160956368485035589278753:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((7078680809:ℚ)/10000000000),((895133601:ℚ)/1250000000),((-5985935207:ℚ)/6853125000),((-86902850517:ℚ)/110125000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3725412813:ℚ)/10000000000),((829163339025329120845243769718300190284321381515351733533:ℚ)/36310258325107383728027343750000000000000000000000000000000),((157154647103200960690258451:ℚ)/693120000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7108376697:ℚ)/10000000000),((896989539:ℚ)/1250000000),((-5998926773:ℚ)/6882812500),((-87288897061:ℚ)/110362500000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((3616544493:ℚ)/10000000000),((1197489975009175391406075420531812061332765580116780374227403:ℚ)/52951664029628714919090270996093750000000000000000000000000000),((157189146341789588862713771:ℚ)/693120000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((3561612307:ℚ)/5000000000),((7190763799:ℚ)/10000000000),((-48095346593:ℚ)/55181250000),((-43740959991:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3560918987:ℚ)/10000000000),((1037539416884512328440824601261861609584571080324839591286703:ℚ)/45878249873490971374511718750000000000000000000000000000000000),((3354104589763531167307481217:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3569036257:ℚ)/5000000000),((720561127:ℚ)/1000000000),((-688561127:ℚ)/790000000),((-43837471341:ℚ)/55418750000),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((876112229:ℚ)/2500000000),((5479207325910614434476644522704269389519126496566197269479:ℚ)/242278406255443750000000000000000000000000000000000000000000),((33548408750000880988013793:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1430584079:ℚ)/2000000000),((288818349:ℚ)/400000000),((-1932128443:ℚ)/2216750000),((-17573593027:ℚ)/22215000000),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3447092719:ℚ)/10000000000),((3377134445571867800636168261390768218096754395906268317731:ℚ)/149327668989496097949218750000000000000000000000000000000000),((16106771092803321871367051:ℚ)/70975488000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((7167768259:ℚ)/10000000000),((1447061233:ℚ)/2000000000),((-3227142877:ℚ)/3702500000),((-88060987367:ℚ)/111312500000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((3388805333:ℚ)/10000000000),((1750501896215506331123233574630705466300007903582388775913:ℚ)/77401558525495800781250000000000000000000000000000000000000),((134252555912578741433170513:ℚ)/591462400000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1436523221:ℚ)/2000000000),((7250153589:ℚ)/10000000000),((-48511075123:ℚ)/55656250000),((-17650801873:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((3329537791:ℚ)/10000000000),((1895214977125288031684611017440096641443994743472995047445159:ℚ)/83799418957037630677223205566406250000000000000000000000000000),((27897927717933511280926211:ℚ)/122880000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2231:ℚ)/3200),((8943:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7197463933:ℚ)/10000000000),((7265000997:ℚ)/10000000000),((-48615006979:ℚ)/55775000000),((-88447031129:ℚ)/111787500000),((961640533:ℚ)/1000000000),((9622019977:ℚ)/10000000000),((555749933:ℚ)/2000000000),((1634618361:ℚ)/5000000000),((85282362448120079112229229439733966319050924881020053792296461:ℚ)/3770833699786057910156250000000000000000000000000000000000000000),((10073362571192382167982775259:ℚ)/44359680000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((8943:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8943:ℚ)/12800),((4481:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1442462349:ℚ)/2000000000),((727984839:ℚ)/1000000000),((-442899443:ℚ)/508125000),((-17728010537:ℚ)/22405000000),((1922169193:ℚ)/2000000000),((1923281067:ℚ)/2000000000),((349868089:ℚ)/1250000000),((3207843767:ℚ)/10000000000),((44683669579096509353890557103083117231875344857847429033:ℚ)/1975708371411935485839843750000000000000000000000000000000),((100755736886460277532387171:ℚ)/443596800000000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((8943:ℚ)/12800) ((4481:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((7227159539:ℚ)/10000000000),((7309543129:ℚ)/10000000000),((-48926801903:ℚ)/56012500000),((-29611024669:ℚ)/37500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3145294929:ℚ)/10000000000),((752306809406306823286959785738424929949419406629880773:ℚ)/32950054922241210937500000000000000000000000000000000000),((3359999093518530265186547297:ℚ)/14786560000000000000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((290274203:ℚ)/400000000),((7339237807:ℚ)/10000000000),((-49134664649:ℚ)/56250000000),((-3568764639:ℚ)/4519000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3016440377:ℚ)/10000000000),((518626945527699494809904526429081710861988680353209021522148673:ℚ)/22716021986389160156250000000000000000000000000000000000000000000),((3361474227346785262912066833:ℚ)/14786560000000000000000000000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1457310109:ℚ)/2000000000),((294757297:ℚ)/400000000),((-1973701079:ℚ)/2259500000),((-17921031417:ℚ)/22690000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((2882013591:ℚ)/10000000000),((2118518404395526251497072302237759482753238250175867050623:ℚ)/92795315949060859179687500000000000000000000000000000000000),((5380719943060392974259153:ℚ)/23658496000000000000000000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7316245947:ℚ)/10000000000),((1857080371:ℚ)/2500000000),((-12439562597:ℚ)/14181250000),((-89991197311:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((685298577:ℚ)/2500000000),((104307155263425168268838311495683436130950797630290767147:ℚ)/4486134212513916015625000000000000000000000000000000000000),((210368953024520498931926297:ℚ)/924160000000000000000000000)⟩
theorem valid19 : Valid ninth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1475127311:ℚ)/2000000000),((7487710311:ℚ)/10000000000),((-50173972177:ℚ)/57200000000),((-18152655043:ℚ)/23070000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2435894647:ℚ)/10000000000),((12058741285397991075486091372494712888943192729886215894237507:ℚ)/518778592718100000000000000000000000000000000000000000000000000),((10106576837031576581324247971:ℚ)/44359680000000000000000000000)⟩
theorem valid20 : Valid ninth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3717513453:ℚ)/5000000000),((235846841:ℚ)/312500000),((-2055823:ℚ)/2343750),((-45767674889:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((208738957:ℚ)/1000000000),((269774000820710489770664814734415879624994928359:ℚ)/11609192848205566406250000000000000000000000000000),((3292790094275292556070177:ℚ)/14440000000000000000000000)⟩
theorem valid21 : Valid ninth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((3747208503:ℚ)/5000000000),((3832937729:ℚ)/5000000000),((-25710564103:ℚ)/29075000000),((-46153710539:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((208602387:ℚ)/1250000000),((322537589444873427754495107194608234585792333726905772303639:ℚ)/13413872004636401367187500000000000000000000000000000000000000),((46737591:ℚ)/204800000)⟩
theorem valid22 : Valid ninth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/8),((-13:ℚ)/16),((3806598239:ℚ)/5000000000),((790342607:ℚ)/1000000000),((-1769466083:ℚ)/1970000000),((-46925777107:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((13654510849885612559701110296680878327433832470197293473:ℚ)/533408117493750000000000000000000000000000000000000000000),((46737591:ℚ)/204800000)⟩
theorem valid23 : Valid ninth packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((3925376333:ℚ)/5000000000),((4189259193:ℚ)/5000000000),((-28204814351:ℚ)/30500000000),((-48469892329:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8288309555987167157183184553052225441452631971509830386063:ℚ)/290863738476562500000000000000000000000000000000000000000000),((46737591:ℚ)/204800000)⟩
theorem valid24 : Valid ninth packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((1665171031:ℚ)/2000000000),((1027879993:ℚ)/1000000000),(-1:ℚ),((-20623223403:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((74441760221836187396845493262688763:ℚ)/1920000000000000000000000000000000000),((46737591:ℚ)/204800000)⟩
theorem valid25 : Valid ninth packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10226167721:ℚ)/10000000000),((1407913041:ℚ)/1000000000),(-1:ℚ),((-42606726791:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((58171244406175327634252459:ℚ)/1354240000000000000000000000),((46737591:ℚ)/204800000)⟩
theorem valid26 : Valid ninth packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet26 valid26
private theorem node1_3 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((4367:ℚ)/6400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((4367:ℚ)/6400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((8829:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound ninth nn0 nn1 Qcell ((4367:ℚ)/6400) ((8829:ℚ)/12800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound ninth nn0 nn1 Qcell ((8829:ℚ)/12800) ((8867:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound ninth nn0 nn1 Qcell ((8867:ℚ)/12800) ((1781:ℚ)/2560) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound ninth nn0 nn1 Qcell ((8829:ℚ)/12800) ((1781:ℚ)/2560) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound ninth nn0 nn1 Qcell ((4367:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1781:ℚ)/2560) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound ninth nn0 nn1 Qcell ((1781:ℚ)/2560) ((4481:ℚ)/6400) :=
  cell_join leaf13 node14_16
private theorem node16_18 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join node16_18 node18_20
private theorem node13_20 :
    CellBound ninth nn0 nn1 Qcell ((1781:ℚ)/2560) ((143:ℚ)/200) :=
  cell_join node13_16 node16_20
private theorem node21_23 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf20 node21_23
private theorem node23_25 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node23_25 node25_27
private theorem node20_27 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node20_23 node23_27
private theorem node13_27 :
    CellBound ninth nn0 nn1 Qcell ((1781:ℚ)/2560) ((69:ℚ)/50) :=
  cell_join node13_20 node20_27
private theorem node0_27 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_27
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_27
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26]
theorem packet_count : packets.length = 27 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC03
#check @N11Formalization.C450NinthGroupedC03.bound
#print axioms N11Formalization.C450NinthGroupedC03.valid0
#print axioms N11Formalization.C450NinthGroupedC03.valid1
#print axioms N11Formalization.C450NinthGroupedC03.valid2
#print axioms N11Formalization.C450NinthGroupedC03.valid3
#print axioms N11Formalization.C450NinthGroupedC03.valid4
#print axioms N11Formalization.C450NinthGroupedC03.valid5
#print axioms N11Formalization.C450NinthGroupedC03.valid6
#print axioms N11Formalization.C450NinthGroupedC03.valid7
#print axioms N11Formalization.C450NinthGroupedC03.valid8
#print axioms N11Formalization.C450NinthGroupedC03.valid9
#print axioms N11Formalization.C450NinthGroupedC03.valid10
#print axioms N11Formalization.C450NinthGroupedC03.valid11
#print axioms N11Formalization.C450NinthGroupedC03.valid12
#print axioms N11Formalization.C450NinthGroupedC03.valid13
#print axioms N11Formalization.C450NinthGroupedC03.valid14
#print axioms N11Formalization.C450NinthGroupedC03.valid15
#print axioms N11Formalization.C450NinthGroupedC03.valid16
#print axioms N11Formalization.C450NinthGroupedC03.valid17
#print axioms N11Formalization.C450NinthGroupedC03.valid18
#print axioms N11Formalization.C450NinthGroupedC03.valid19
#print axioms N11Formalization.C450NinthGroupedC03.valid20
#print axioms N11Formalization.C450NinthGroupedC03.valid21
#print axioms N11Formalization.C450NinthGroupedC03.valid22
#print axioms N11Formalization.C450NinthGroupedC03.valid23
#print axioms N11Formalization.C450NinthGroupedC03.valid24
#print axioms N11Formalization.C450NinthGroupedC03.valid25
#print axioms N11Formalization.C450NinthGroupedC03.valid26
#print axioms N11Formalization.C450NinthGroupedC03.bound
#print axioms N11Formalization.C450NinthGroupedC03.endpoint_checks
