import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6832616947:ℚ)/10000000000),((1760861933:ℚ)/2500000000),((-19371205129:ℚ)/24800000000),((-16817850841:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4532503787:ℚ)/10000000000),((11917400974495510494874720162010943517869003199077601166966429:ℚ)/48720010737600000000000000000000000000000000000000000000000000),((354388311916044096581804687:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3475941891:ℚ)/5000000000),((88787947:ℚ)/125000000),((-978243311:ℚ)/1263750000),((-8587825673:ℚ)/12756250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2079890161:ℚ)/5000000000),((3900351932951171890468765029464476777578806993089437859:ℚ)/16420998228929180145263671875000000000000000000000000000),((265950469968231403997175949:ℚ)/443596800000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7011509937:ℚ)/10000000000),((3566414143:ℚ)/5000000000),((-39323383859:ℚ)/51025000000),((-17354529811:ℚ)/25631250000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((61892901:ℚ)/156250000),((136197797689221127774464113522233242244074681215245062141328117:ℚ)/581831666644356774902343750000000000000000000000000000000000000),((1064113583510626519223909701:ℚ)/1774387200000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((3520660629:ℚ)/5000000000),((3581309919:ℚ)/5000000000),((-39517028947:ℚ)/51262500000),((-8721981887:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3858213911:ℚ)/10000000000),((3136842225930588416538374893953545607145326774414178608811909:ℚ)/13398157312707073974609375000000000000000000000000000000000000),((266172144308853392200532989:ℚ)/443596800000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((707113143:ℚ)/1000000000),((7192410429:ℚ)/10000000000),((-79421335577:ℚ)/103000000000),((-1753339429:ℚ)/2586875000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((938152247:ℚ)/2500000000),((410954808584701655526940579170088388514675133809687558377012231:ℚ)/1754986593971906250000000000000000000000000000000000000000000000),((10652624226936314451061621:ℚ)/17743872000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7100940469:ℚ)/10000000000),((3611100037:ℚ)/5000000000),((-39904300481:ℚ)/51737500000),((-17622821407:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((1822048969:ℚ)/5000000000),((9956653517138739855445276457116381803529569788832543268877959:ℚ)/42513087056230604553222656250000000000000000000000000000000000),((355278373431745489241695423:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-13:ℚ)/16),((-3:ℚ)/4),((7130748391:ℚ)/10000000000),((1447418909:ℚ)/2000000000),((-1777827313:ℚ)/2310000000),((-17712245173:ℚ)/26046875000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((3532412377:ℚ)/10000000000),((2666929258874618572690629686801298781498137246482319283057:ℚ)/11468863513258593750000000000000000000000000000000000000000),((355328625483178488327310983:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7145651937:ℚ)/10000000000),((1450397757:ℚ)/2000000000),((-16039170841:ℚ)/20837500000),((-17756955811:ℚ)/26106250000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((139011347:ℚ)/400000000),((28680724077875054602960866874900333352188493702382060299928541:ℚ)/123326333301820109558105468750000000000000000000000000000000000),((1066271227794896284360241701:ℚ)/1774387200000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((716055521:ℚ)/1000000000),((3633441397:ℚ)/5000000000),((-40194738161:ℚ)/52212500000),((-1780166563:ℚ)/2616562500),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((1708620239:ℚ)/5000000000),((1813228598775242857042783453360932739451486586889403574172434941:ℚ)/7796069060184567347717285156250000000000000000000000000000000000),((3555187641059964507067063:ℚ)/5914624000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7175458211:ℚ)/10000000000),((3640888287:ℚ)/5000000000),((-40291547731:ℚ)/52331250000),((-17846374633:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1679117649:ℚ)/5000000000),((28657824680100344743287481839806155124313149531494879522745471:ℚ)/123203865057399352455139160156250000000000000000000000000000000),((355613690027241076898875503:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((3595180471:ℚ)/5000000000),((7296670127:ℚ)/10000000000),((-80776711651:ℚ)/104900000000),((-8945541413:ℚ)/13142187500),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((3298216429:ℚ)/10000000000),((59365218236204224217299904914269557083373536556273788965862709279:ℚ)/255194759756792903125000000000000000000000000000000000000000000000),((88927130094981329516564263:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((1441052681:ℚ)/2000000000),((1462312691:ℚ)/2000000000),((-16194064983:ℚ)/21027500000),((-3587158043:ℚ)/5268750000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((323712741:ℚ)/1000000000),((5337363194603998602861461913012164533241093391583555582923:ℚ)/22941699475712056152343750000000000000000000000000000000000),((14232130207275646541030823:ℚ)/23658496000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((3610082801:ℚ)/5000000000),((3663228279:ℚ)/5000000000),((-40581967627:ℚ)/52687500000),((-8990248403:ℚ)/13201562500),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((3174906391:ℚ)/10000000000),((111639005694926669237994897374229155124685967707716522330727799:ℚ)/479815756052087974548339843750000000000000000000000000000000000),((88974473608023791727521943:ℚ)/147865600000000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3617533767:ℚ)/5000000000),((7341349439:ℚ)/10000000000),((-11622506101:ℚ)/15087500000),((-9012601301:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3111485387:ℚ)/10000000000),((385946196078356763185319642375292505115891702286133912664589:ℚ)/1658615001708758544921875000000000000000000000000000000000000),((266994328620574308253120981:ℚ)/443596800000000000000000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1812492301:ℚ)/2500000000),((7371134539:ℚ)/10000000000),((-81744749007:ℚ)/105850000000),((-4517476903:ℚ)/6645312500),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((11901521:ℚ)/39062500),((15711777948225208356616991849715111268532891513389329165434217483:ℚ)/67036815295923639453125000000000000000000000000000000000000000000),((22264195878728945356988943:ℚ)/36966400000000000000000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((7279771763:ℚ)/10000000000),((7400918767:ℚ)/10000000000),((-82131943971:ℚ)/106325000000),((-18159315289:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((2913230579:ℚ)/10000000000),((15692384178251103703155217751993018674226243091370696035061871:ℚ)/66945089612122229003906250000000000000000000000000000000000000),((356415739899792909607777167:ℚ)/591462400000000000000000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1827393323:ℚ)/2500000000),((7430702133:ℚ)/10000000000),((-82519127729:ℚ)/106800000000),((-4562179969:ℚ)/6704687500),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((554688649:ℚ)/2000000000),((256760000041639250391930229117843827252754095951531676812226061:ℚ)/1095218660690634375000000000000000000000000000000000000000000000),((22287747742844613113282047:ℚ)/36966400000000000000000000)⟩
theorem valid16 : Valid source24 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((3669686903:ℚ)/5000000000),((7460484651:ℚ)/10000000000),((-11843757209:ℚ)/15325000000),((-9169060709:ℚ)/13468750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((328304039:ℚ)/1250000000),((5740745246238743512625013762789247667010876817744596834743:ℚ)/24484277946348381042480468750000000000000000000000000000000),((89197951535257142865080487:ℚ)/147865600000000000000000000)⟩
theorem valid17 : Valid source24 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source24 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3684586659:ℚ)/5000000000),((7520047183:ℚ)/10000000000),((-83680613379:ℚ)/107750000000),((-9213759977:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2470908001:ℚ)/10000000000),((1098131450755244678080869821400394531659708256852842721093907759:ℚ)/4619138096331982421875000000000000000000000000000000000000000000),((267944793148703159886601549:ℚ)/443596800000000000000000000)⟩
theorem valid18 : Valid source24 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((1857192347:ℚ)/2500000000),((3819581269:ℚ)/5000000000),((-42614556497:ℚ)/54350000000),((-4651577041:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((132922259:ℚ)/625000000),((22224294429218231609542915628267478514433257110093278470769:ℚ)/91035989906854248046875000000000000000000000000000000000000),((22364096208547443792171487:ℚ)/36966400000000000000000000)⟩
theorem valid19 : Valid source24 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((3773975037:ℚ)/5000000000),((7877356681:ℚ)/10000000000),((-88325636853:ℚ)/110600000000),((-9481925111:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1171025721:ℚ)/10000000000),((243563171431404988812478235016480131165932551497156395851347:ℚ)/950049175075000000000000000000000000000000000000000000000000),((268085094926776017313884301:ℚ)/443596800000000000000000000)⟩
theorem valid20 : Valid source24 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((3893134153:ℚ)/5000000000),((1103715589:ℚ)/1250000000),((-12588302657:ℚ)/14300000000),((-9839402459:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1624095775628036753474668631948384091142060034801802754031:ℚ)/4996281803906250000000000000000000000000000000000000000000),((618558677:ℚ)/1024000000)⟩
theorem valid21 : Valid source24 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((8739059349:ℚ)/10000000000),((1956318821:ℚ)/2000000000),((-7538714891:ℚ)/8640000000),((-22537178047:ℚ)/36200000000),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),(0:ℚ),((3882089824341698115240700372979341371066236431613139932117:ℚ)/12380827449600000000000000000000000000000000000000000000000),((618558677:ℚ)/1024000000)⟩
theorem valid22 : Valid source24 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((302851949:ℚ)/312500000),((5366553729:ℚ)/5000000000),((-62725198477:ℚ)/72400000000),((-793555847:ℚ)/1250000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((90455989896930785337947573038433356964929518359276435297:ℚ)/296487050000000000000000000000000000000000000000000000000),((618558677:ℚ)/1024000000)⟩
theorem valid23 : Valid source24 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source24 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨(1:ℚ),((119:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((17028873:ℚ)/16000000),((12635407987:ℚ)/10000000000),((-150180303831:ℚ)/160000000000),((-45198619:ℚ)/76160000),((4638999999:ℚ)/5000000000),((4772478993:ℚ)/5000000000),((1911621469:ℚ)/5000000000),(0:ℚ),((16653426678952738684355906556239050453062932195166409243184091:ℚ)/45315200000000000000000000000000000000000000000000000000000000),((618558677:ℚ)/1024000000)⟩
theorem valid24 : Valid source24 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((119:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((119:ℚ)/100),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((12545756179:ℚ)/10000000000),((14537074189:ℚ)/10000000000),((-174901964457:ℚ)/190400000000),((-33957268537:ℚ)/55200000000),((9544957981:ℚ)/10000000000),(1:ℚ),((189269891:ℚ)/625000000),(0:ℚ),((205442459835632110454714131104879706649153:ℚ)/586828214784000000000000000000000000000000),((618558677:ℚ)/1024000000)⟩
theorem valid25 : Valid source24 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source24 nn0 nn1 Qcell ((119:ℚ)/100) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet25 valid25
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4101:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source24 nn0 nn1 Qcell ((4101:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((1667:ℚ)/2560) ((8373:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((8373:ℚ)/12800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source24 nn0 nn1 Qcell ((8373:ℚ)/12800) ((8411:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source24 nn0 nn1 Qcell ((8411:ℚ)/12800) ((8449:ℚ)/12800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source24 nn0 nn1 Qcell ((8373:ℚ)/12800) ((8449:ℚ)/12800) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((8449:ℚ)/12800) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((8449:ℚ)/12800) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source24 nn0 nn1 Qcell ((8449:ℚ)/12800) ((267:ℚ)/400) :=
  cell_join leaf13 node14_16
private theorem node17_19 :
    CellBound source24 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf16 node17_19
private theorem node13_19 :
    CellBound source24 nn0 nn1 Qcell ((8449:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_join node13_16 node16_19
private theorem node20_22 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf19 node20_22
private theorem node22_24 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join node22_24 node24_26
private theorem node19_26 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node19_22 node22_26
private theorem node13_26 :
    CellBound source24 nn0 nn1 Qcell ((8449:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node13_19 node19_26
private theorem node0_26 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_26
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_26
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25]
theorem packet_count : packets.length = 26 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC04
#check @N11Formalization.C450Source24GroupedC04.bound
#print axioms N11Formalization.C450Source24GroupedC04.valid0
#print axioms N11Formalization.C450Source24GroupedC04.valid1
#print axioms N11Formalization.C450Source24GroupedC04.valid2
#print axioms N11Formalization.C450Source24GroupedC04.valid3
#print axioms N11Formalization.C450Source24GroupedC04.valid4
#print axioms N11Formalization.C450Source24GroupedC04.valid5
#print axioms N11Formalization.C450Source24GroupedC04.valid6
#print axioms N11Formalization.C450Source24GroupedC04.valid7
#print axioms N11Formalization.C450Source24GroupedC04.valid8
#print axioms N11Formalization.C450Source24GroupedC04.valid9
#print axioms N11Formalization.C450Source24GroupedC04.valid10
#print axioms N11Formalization.C450Source24GroupedC04.valid11
#print axioms N11Formalization.C450Source24GroupedC04.valid12
#print axioms N11Formalization.C450Source24GroupedC04.valid13
#print axioms N11Formalization.C450Source24GroupedC04.valid14
#print axioms N11Formalization.C450Source24GroupedC04.valid15
#print axioms N11Formalization.C450Source24GroupedC04.valid16
#print axioms N11Formalization.C450Source24GroupedC04.valid17
#print axioms N11Formalization.C450Source24GroupedC04.valid18
#print axioms N11Formalization.C450Source24GroupedC04.valid19
#print axioms N11Formalization.C450Source24GroupedC04.valid20
#print axioms N11Formalization.C450Source24GroupedC04.valid21
#print axioms N11Formalization.C450Source24GroupedC04.valid22
#print axioms N11Formalization.C450Source24GroupedC04.valid23
#print axioms N11Formalization.C450Source24GroupedC04.valid24
#print axioms N11Formalization.C450Source24GroupedC04.valid25
#print axioms N11Formalization.C450Source24GroupedC04.bound
#print axioms N11Formalization.C450Source24GroupedC04.endpoint_checks
