import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((6374243903:ℚ)/10000000000),((832744779:ℚ)/1250000000),((-2418234337:ℚ)/2480000000),((-42699707321:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1439686687:ℚ)/2500000000),((4522942560140198053030341422815802521491:ℚ)/316052719000000000000000000000000000000000),((41803472187032309645130887:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((6611771801:ℚ)/10000000000),((3390359023:ℚ)/5000000000),((-9851077069:ℚ)/10300000000),((-44362402607:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5156549019:ℚ)/10000000000),((190862129215775352222926154927336161517254324557285305109:ℚ)/14678196820397949218750000000000000000000000000000000000000),((41862982604867183209747543:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((420658437:ℚ)/625000000),((689947751:ℚ)/1000000000),((-2005843253:ℚ)/2098000000),((-941536353:ℚ)/1112500000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((966038267:ℚ)/2000000000),((2963779003045042013280926324277125725399980352774197397:ℚ)/228584346518225000000000000000000000000000000000000000000),((1965158358840419997494479:ℚ)/10830000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((6849297713:ℚ)/10000000000),((6958857117:ℚ)/10000000000),((-20236571351:ℚ)/21360000000),((-46025083991:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4482119949:ℚ)/10000000000),((210071624254097945213325424740069286635473168192548068515717:ℚ)/16971864734606400000000000000000000000000000000000000000000000),((41953091753062614170572167:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3454339453:ℚ)/5000000000),((1754559161:ℚ)/2500000000),((-5103677483:ℚ)/5387500000),((-23220376171:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4298297757:ℚ)/10000000000),((7141108352102755186040648228694717925948162382431230750123:ℚ)/577392262041497802734375000000000000000000000000000000000000),((10495818734428804739920287:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((696805999:ℚ)/1000000000),((1769404023:ℚ)/2500000000),((-5148212069:ℚ)/5435000000),((-4685641993:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2053394463:ℚ)/5000000000),((1863659994128925174074202528597980459036089700964785319941:ℚ)/150801599388116381835937500000000000000000000000000000000000),((420134539192869350116743:ℚ)/2310400000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((7027440969:ℚ)/10000000000),((7107305787:ℚ)/10000000000),((-20681917361:ℚ)/21930000000),((-47272086783:ℚ)/55062500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3906459471:ℚ)/10000000000),((7187539962363544366848969245342541113932980170085224603323:ℚ)/594907272398559375000000000000000000000000000000000000000000),((126084888032420515861480069:ℚ)/693120000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((352856571:ℚ)/500000000),((7136995463:ℚ)/10000000000),((-20770986389:ℚ)/22025000000),((-2373995997:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((760510523:ℚ)/2000000000),((17618831592227578295451461821583360776053880475031435472963:ℚ)/1458646302722998046875000000000000000000000000000000000000000),((315325363760978762958139:ℚ)/1732800000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1417364369:ℚ)/2000000000),((7166685121:ℚ)/10000000000),((-2980007909:ℚ)/3160000000),((-9537550583:ℚ)/11107500000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3695871517:ℚ)/10000000000),((7835508267998151203302710695932407562129933728809440081967:ℚ)/648847508447400000000000000000000000000000000000000000000000),((1682338664356983768695623:ℚ)/9241600000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((1423302449:ℚ)/2000000000),((7181529943:ℚ)/10000000000),((-20904589829:ℚ)/22215000000),((-9579117143:ℚ)/11131250000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((3586168111:ℚ)/10000000000),((1297726380650109970260741615440344005465266715202903150312861:ℚ)/108671788169796104296875000000000000000000000000000000000000000),((1682635359980612745449543:ℚ)/9241600000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((1782839359:ℚ)/2500000000),((179909369:ℚ)/250000000),((-523728107:ℚ)/556562500),((-11999875513:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((3530095139:ℚ)/10000000000),((500312112531029660272167676851371827678923668766676373:ℚ)/41899709478518815338611602783203125000000000000000000000),((2629589091867394620686583:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2231:ℚ)/3200),((8943:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7146202621:ℚ)/10000000000),((7211219573:ℚ)/10000000000),((-20993658719:ℚ)/22310000000),((-48103418347:ℚ)/55893750000),((961640533:ℚ)/1000000000),((9622019977:ℚ)/10000000000),((555749933:ℚ)/2000000000),((1736577759:ℚ)/5000000000),((130975051048147445741175084934547203751434335612372026233483:ℚ)/10969698035741259375000000000000000000000000000000000000000000),((42080966678031245502655263:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((8943:ℚ)/12800) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8943:ℚ)/12800),((4481:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7161047799:ℚ)/10000000000),((3613032191:ℚ)/5000000000),((-10519096573:ℚ)/11178750000),((-48207334593:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((1923281067:ℚ)/2000000000),((349868089:ℚ)/1250000000),((1707652921:ℚ)/5000000000),((125579542743030362507601764755183307769211725612232330052839:ℚ)/10518671369397144526611328125000000000000000000000000000000000),((126265522871948650954665829:ℚ)/693120000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((8943:ℚ)/12800) ((4481:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4481:ℚ)/6400),((8981:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1793973243:ℚ)/2500000000),((3620454593:ℚ)/5000000000),((-10541363779:ℚ)/11202500000),((-12077812701:ℚ)/14032812500),((4802670763:ℚ)/5000000000),((961084597:ℚ)/1000000000),((563760281:ℚ)/2000000000),((671299797:ℚ)/2000000000),((42302554646659038738212832457546765980653161903377631991451:ℚ)/3543596566517278027832031250000000000000000000000000000000000),((7893009057600041275548721:ℚ)/43320000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((8981:ℚ)/12800) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8981:ℚ)/12800),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((7190738139:ℚ)/10000000000),((1451150797:ℚ)/2000000000),((-4225452391:ℚ)/4490500000),((-5379462997:ℚ)/6250000000),((599993229:ℚ)/625000000),((9605341531:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((206042729:ℚ)/625000000),((482528446639475081145034323178369194621933625792953:ℚ)/40423702016796875000000000000000000000000000000000000),((126310766183076023188838509:ℚ)/693120000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((8981:ℚ)/12800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((9019:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7205583299:ℚ)/10000000000),((363529939:ℚ)/500000000),((-1058589817:ℚ)/1125000000),((-48519083093:ℚ)/56368750000),((1918899207:ℚ)/2000000000),((9599891669:ℚ)/10000000000),((357191541:ℚ)/1250000000),((808950973:ℚ)/2500000000),((4319922093786399937483179566375364715898887562945926323593:ℚ)/361929816705322265625000000000000000000000000000000000000000),((42111128885983500950618943:ℚ)/231040000000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((9019:ℚ)/12800) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((9019:ℚ)/12800),((4519:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3610214227:ℚ)/5000000000),((7285443571:ℚ)/10000000000),((-21216330713:ℚ)/22547500000),((-24311499589:ℚ)/28243750000),((9589154297:ℚ)/10000000000),((239862401:ℚ)/250000000),((575284399:ℚ)/2000000000),((3173798337:ℚ)/10000000000),((17545509398511561647088494446406017788565509943789566527:ℚ)/1470108942829172027587890625000000000000000000000000000000),((10529667195514504507947047:ℚ)/57760000000000000000000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((9019:ℚ)/12800) ((4519:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7235273603:ℚ)/10000000000),((7315133139:ℚ)/10000000000),((-21305399417:ℚ)/22595000000),((-48726915221:ℚ)/56725000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((48603119:ℚ)/156250000),((559662409437447142065327344737023414587062033826136926262913:ℚ)/46397657974530429589843750000000000000000000000000000000000000),((42133874730484523214683487:ℚ)/231040000000000000000000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7264963883:ℚ)/10000000000),((734482269:ℚ)/1000000000),((-2139446807:ℚ)/2269000000),((-48934747181:ℚ)/56962500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((59606347:ℚ)/200000000),((365684208787897395740627472894326517213135500563271634967:ℚ)/30322957541955017625000000000000000000000000000000000000000),((42148953205913217391950927:ℚ)/231040000000000000000000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((7294654139:ℚ)/10000000000),((230453507:ℚ)/312500000),((-21656791:ℚ)/22968750),((-49142578973:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((711064697:ℚ)/2500000000),((124160574134707900576191329231745849007685707453357:ℚ)/10297775280761718750000000000000000000000000000000000),((42164030631996582656243503:ℚ)/231040000000000000000000000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7324344373:ℚ)/10000000000),((7433891241:ℚ)/10000000000),((-21661673723:ℚ)/22880000000),((-49350410611:ℚ)/57675000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2701550701:ℚ)/10000000000),((204296350499788554265864784514194999964295014983821577932649:ℚ)/16600914966979200000000000000000000000000000000000000000000000),((42194439605821403948332847:ℚ)/231040000000000000000000000)⟩
theorem valid20 : Valid seventh packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7383724773:ℚ)/10000000000),((7493270193:ℚ)/10000000000),((-21839810579:ℚ)/23070000000),((-49766073411:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((298921341:ℚ)/1250000000),((8510193101371109124520357938898243368441772815583117014113:ℚ)/691975903363336125000000000000000000000000000000000000000000),((126673767585614827092892141:ℚ)/693120000000000000000000000)⟩
theorem valid21 : Valid seventh packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((1488621017:ℚ)/2000000000),((3806013953:ℚ)/5000000000),((-11098041859:ℚ)/11630000000),((-10036347119:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((508865049:ℚ)/2500000000),((5486309355558247454768626095075292705920020254314730650379:ℚ)/429243904148364843750000000000000000000000000000000000000000),((1691167524075125987864727:ℚ)/9241600000000000000000000)⟩
theorem valid22 : Valid seventh packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-15:ℚ)/16),((-7:ℚ)/8),((1890466363:ℚ)/2500000000),((1962385653:ℚ)/2500000000),((-5727156959:ℚ)/5910000000),((-12753264541:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((501094081:ℚ)/5000000000),((98724178027186230404282375508397852230134348553437563613:ℚ)/7201009586165625000000000000000000000000000000000000000000),((2642383508147059131000367:ℚ)/14440000000000000000000000)⟩
theorem valid23 : Valid seventh packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((7799385219:ℚ)/10000000000),((2081142359:ℚ)/2500000000),((-6083427077:ℚ)/6100000000),((-17558565511:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1995603417088501343837747043501505864145758552233841733:ℚ)/129272772656250000000000000000000000000000000000000000000),((23422601:ℚ)/128000000)⟩
theorem valid24 : Valid seventh packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((8274421273:ℚ)/10000000000),((5112325623:ℚ)/5000000000),(-1:ℚ),((-56000948911:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((44119788909265732508352420445213351:ℚ)/2400000000000000000000000000000000000),((23422601:ℚ)/128000000)⟩
theorem valid25 : Valid seventh packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((10174531237:ℚ)/10000000000),((14024747283:ℚ)/10000000000),(-1:ℚ),((-69301718659:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((12598091289099744663689447:ℚ)/609408000000000000000000000),((23422601:ℚ)/128000000)⟩
theorem valid26 : Valid seventh packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet26 valid26
private theorem node1_3 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound seventh nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((4443:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound seventh nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((8981:ℚ)/12800) ((9019:ℚ)/12800) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((9019:ℚ)/12800) :=
  cell_join leaf13 node14_16
private theorem node16_18 :
    CellBound seventh nn0 nn1 Qcell ((9019:ℚ)/12800) ((2269:ℚ)/3200) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound seventh nn0 nn1 Qcell ((9019:ℚ)/12800) ((143:ℚ)/200) :=
  cell_join node16_18 node18_20
private theorem node13_20 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join node13_16 node16_20
private theorem node21_23 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf20 node21_23
private theorem node23_25 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node23_25 node25_27
private theorem node20_27 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node20_23 node23_27
private theorem node13_27 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node13_20 node20_27
private theorem node0_27 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_27
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_27
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26]
theorem packet_count : packets.length = 27 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC02
#check @N11Formalization.C450SeventhGroupedC02.bound
#print axioms N11Formalization.C450SeventhGroupedC02.valid0
#print axioms N11Formalization.C450SeventhGroupedC02.valid1
#print axioms N11Formalization.C450SeventhGroupedC02.valid2
#print axioms N11Formalization.C450SeventhGroupedC02.valid3
#print axioms N11Formalization.C450SeventhGroupedC02.valid4
#print axioms N11Formalization.C450SeventhGroupedC02.valid5
#print axioms N11Formalization.C450SeventhGroupedC02.valid6
#print axioms N11Formalization.C450SeventhGroupedC02.valid7
#print axioms N11Formalization.C450SeventhGroupedC02.valid8
#print axioms N11Formalization.C450SeventhGroupedC02.valid9
#print axioms N11Formalization.C450SeventhGroupedC02.valid10
#print axioms N11Formalization.C450SeventhGroupedC02.valid11
#print axioms N11Formalization.C450SeventhGroupedC02.valid12
#print axioms N11Formalization.C450SeventhGroupedC02.valid13
#print axioms N11Formalization.C450SeventhGroupedC02.valid14
#print axioms N11Formalization.C450SeventhGroupedC02.valid15
#print axioms N11Formalization.C450SeventhGroupedC02.valid16
#print axioms N11Formalization.C450SeventhGroupedC02.valid17
#print axioms N11Formalization.C450SeventhGroupedC02.valid18
#print axioms N11Formalization.C450SeventhGroupedC02.valid19
#print axioms N11Formalization.C450SeventhGroupedC02.valid20
#print axioms N11Formalization.C450SeventhGroupedC02.valid21
#print axioms N11Formalization.C450SeventhGroupedC02.valid22
#print axioms N11Formalization.C450SeventhGroupedC02.valid23
#print axioms N11Formalization.C450SeventhGroupedC02.valid24
#print axioms N11Formalization.C450SeventhGroupedC02.valid25
#print axioms N11Formalization.C450SeventhGroupedC02.valid26
#print axioms N11Formalization.C450SeventhGroupedC02.bound
#print axioms N11Formalization.C450SeventhGroupedC02.endpoint_checks
