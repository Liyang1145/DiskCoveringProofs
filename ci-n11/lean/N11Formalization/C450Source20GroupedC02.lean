import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((106565529:ℚ)/156250000),((7025712957:ℚ)/10000000000),((-18773138871:ℚ)/19840000000),((-650958703:ℚ)/789843750),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((285605707:ℚ)/625000000),((99734874721856999825206733332728833569450933:ℚ)/1039360229068800000000000000000000000000000000),((2147321155450097138024925567:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((6939128429:ℚ)/10000000000),((7085139547:ℚ)/10000000000),((-6317139547:ℚ)/6740000000),((-42493899003:ℚ)/51025000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((840224251:ℚ)/2000000000),((133773773684779124333561510777225384361946567827610307477:ℚ)/1474039201089062500000000000000000000000000000000000000000),((2152010081352846903562982447:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1749648283:ℚ)/2500000000),((7114852483:ℚ)/10000000000),((-19040557449:ℚ)/20410000000),((-10727537981:ℚ)/12815625000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((1001241359:ℚ)/2500000000),((40448190597578342585765112278885698678924615647834740454089:ℚ)/458304328187554875000000000000000000000000000000000000000000),((2154356102442702662956601087:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((7028324859:ℚ)/10000000000),((111633831:ℚ)/156250000),((-99633831:ℚ)/106796875),((-43118274013:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3903404093:ℚ)/10000000000),((911929664466113125190504189488534644231556475582965299:ℚ)/10338084346224594116210937500000000000000000000000000000),((526538858056602594017463:ℚ)/722000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7058056177:ℚ)/10000000000),((7174277653:ℚ)/10000000000),((-19218832959:ℚ)/20600000000),((-43326393239:ℚ)/51737500000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((949818229:ℚ)/2500000000),((161177053203712398866255693688135021530064252601154627997561:ℚ)/1828111035387402343750000000000000000000000000000000000000000),((2159051262036312870478788047:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((1771946773:ℚ)/2500000000),((3601994947:ℚ)/5000000000),((-9653984841:ℚ)/10347500000),((-10883627411:ℚ)/12993750000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((923088497:ℚ)/2500000000),((837274617346764609790271754007012307032288306110469701953:ℚ)/9501337551614712890625000000000000000000000000000000000000),((540350100260914502362533247:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((7117517609:ℚ)/10000000000),((721884593:ℚ)/1000000000),((-645084593:ℚ)/693000000),((-43742623263:ℚ)/52093750000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((3582397197:ℚ)/10000000000),((1087550570274629998631061514758708851000536543788268753:ℚ)/12511487469009375000000000000000000000000000000000000000),((21625753604578995822564967:ℚ)/29573120000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7132382721:ℚ)/10000000000),((723370191:ℚ)/1000000000),((-1939710573:ℚ)/2083750000),((-43846679047:ℚ)/52212500000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((705238187:ℚ)/2000000000),((42871479390230477095167060251788833328489442792824669354667:ℚ)/493305333207280438232421875000000000000000000000000000000000),((21637505798348823550718823:ℚ)/29573120000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1429449547:ℚ)/2000000000),((3624278917:ℚ)/5000000000),((-9720836751:ℚ)/10442500000),((-2930048943:ℚ)/3488750000),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((867278289:ℚ)/2500000000),((2408510657928380127950474604475226955424046084459423521091801:ℚ)/27719356658434017236328125000000000000000000000000000000000000),((541231514792904109698731887:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1790528163:ℚ)/2500000000),((7263413703:ℚ)/10000000000),((-6495413703:ℚ)/6977500000),((-11013697141:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((852780011:ℚ)/2500000000),((101479738985544509530444762983792509327523789166863210072497:ℚ)/1168155164988675341796875000000000000000000000000000000000000),((2166101798544263943694263447:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7176977473:ℚ)/10000000000),((7278269517:ℚ)/10000000000),((-19530808551:ℚ)/20980000000),((-44158842311:ℚ)/52568750000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((3352164023:ℚ)/10000000000),((177318699652056437943996485255882613804108319137787927947736969:ℚ)/2041558078054343225000000000000000000000000000000000000000000000),((2167277797949888393486085087:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((7191842199:ℚ)/10000000000),((7293125277:ℚ)/10000000000),((-19575375831:ℚ)/21027500000),((-44262895393:ℚ)/52687500000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((3292193293:ℚ)/10000000000),((448245043339417887297753019501814881958038059677913138510649:ℚ)/5161882382035212634277343750000000000000000000000000000000000),((2168454057464740904313116607:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7206706829:ℚ)/10000000000),((7307980983:ℚ)/10000000000),((-6539980983:ℚ)/7025000000),((-2609820459:ℚ)/3106250000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((807787823:ℚ)/2500000000),((929360812381249514543982399590629829120633661538874549273:ℚ)/10704386365955078125000000000000000000000000000000000000000),((2169630577085938411523124087:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3610785683:ℚ)/5000000000),((1464567327:ℚ)/2000000000),((-3932901981:ℚ)/4224500000),((-22235499781:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1584488017:ℚ)/5000000000),((5391469053347743974492975043960289373129485906851524718243:ℚ)/62111034059282903515625000000000000000000000000000000000000),((86832294272423914437747207:ℚ)/118292480000000000000000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((723643581:ℚ)/1000000000),((7337692233:ℚ)/10000000000),((-19709076699:ℚ)/21170000000),((-4457505067:ℚ)/5304375000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((1552799693:ℚ)/5000000000),((5148411078247478232457029903252449844715083876590625976992149:ℚ)/59322370824313853906250000000000000000000000000000000000000000),((2171984396635836208882164087:ℚ)/2957312000000000000000000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((22660313:ℚ)/31250000),((7352547779:ℚ)/10000000000),((-6584547779:ℚ)/7072500000),((-279244382:ℚ)/332265625),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1520473083:ℚ)/5000000000),((144593930326607836163793089899511356475393833913809557634463:ℚ)/1666396748152470300292968750000000000000000000000000000000000),((2173161696717287957508600703:ℚ)/2957312000000000000000000000)⟩
theorem valid15 : Valid source20 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source20 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((7266164419:ℚ)/10000000000),((7382258713:ℚ)/10000000000),((-19842776139:ℚ)/21265000000),((-44783150933:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((1487466531:ℚ)/5000000000),((11764947568175330365985192353660770777471125147157759343229:ℚ)/133890179224244458007812500000000000000000000000000000000000),((2175517077479137967829952727:ℚ)/2957312000000000000000000000)⟩
theorem valid16 : Valid source20 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source20 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7295892661:ℚ)/10000000000),((3705984719:ℚ)/5000000000),((-37325671:ℚ)/40000000),((-44991248627:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((354805683:ℚ)/1250000000),((970314387808861680738451696613810179120181404128989683:ℚ)/11047608600000000000000000000000000000000000000000000000),((544468374788263612701986663:ℚ)/739328000000000000000000000)⟩
theorem valid17 : Valid source20 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((3662810271:ℚ)/5000000000),((7441679959:ℚ)/10000000000),((-20021039877:ℚ)/21455000000),((-22599671897:ℚ)/26937500000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((539050341:ℚ)/2000000000),((503315033706874411886359354509224108014768014608304266155323:ℚ)/5733107941101223046875000000000000000000000000000000000000000),((2180230962113548672628810423:ℚ)/2957312000000000000000000000)⟩
theorem valid18 : Valid source20 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source20 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3677674033:ℚ)/5000000000),((7501100397:ℚ)/10000000000),((-20199301191:ℚ)/21550000000),((-22703718231:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1272109521:ℚ)/5000000000),((3323523346100176008617460615357212136008542807742043040891361:ℚ)/36953104770655859375000000000000000000000000000000000000000000),((2184949012442634620837311647:ℚ)/2957312000000000000000000000)⟩
theorem valid19 : Valid source20 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7414802063:ℚ)/10000000000),((7619938927:ℚ)/10000000000),((-20555816781:ℚ)/21740000000),((-45823614441:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2212137683:ℚ)/10000000000),((8253822566978229074868843657442492785573802248706365469893:ℚ)/87671993327439062500000000000000000000000000000000000000000),((759283633:ℚ)/1024000000)⟩
theorem valid20 : Valid source20 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((7533705977:ℚ)/10000000000),((7857607157:ℚ)/10000000000),((-21268821471:ℚ)/22120000000),((-3588918603:ℚ)/4400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1321787341:ℚ)/10000000000),((59762464795565250774298588079725567220362885253753175767:ℚ)/584645646200000000000000000000000000000000000000000000000),((759283633:ℚ)/1024000000)⟩
theorem valid21 : Valid source20 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((194287461:ℚ)/250000000),((1101022667:ℚ)/1250000000),(-1:ℚ),((-1208012227:ℚ)/1620000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((425230269410531120131798365893141:ℚ)/3280500000000000000000000000000000),((759283633:ℚ)/1024000000)⟩
theorem valid22 : Valid source20 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((4361248261:ℚ)/5000000000),((10709002203:ℚ)/10000000000),(-1:ℚ),((-27488737827:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((208565201770301526339612226131335227:ℚ)/1500000000000000000000000000000000000),((759283633:ℚ)/1024000000)⟩
theorem valid23 : Valid source20 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((10623923151:ℚ)/10000000000),((1813745697:ℚ)/1250000000),(-1:ℚ),((-68287462057:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((239361761250668875800001499:ℚ)/1523520000000000000000000000),((759283633:ℚ)/1024000000)⟩
theorem valid24 : Valid source20 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet24 valid24
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4101:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((4101:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((1667:ℚ)/2560) ((8373:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((2079:ℚ)/3200) ((8373:ℚ)/12800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source20 nn0 nn1 Qcell ((8373:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source20 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((843:ℚ)/1280) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source20 nn0 nn1 Qcell ((8449:ℚ)/12800) ((8487:ℚ)/12800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source20 nn0 nn1 Qcell ((843:ℚ)/1280) ((8487:ℚ)/12800) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source20 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source20 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source20 nn0 nn1 Qcell ((843:ℚ)/1280) ((4291:ℚ)/6400) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf18 node19_21
private theorem node21_23 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node21_23 node23_25
private theorem node18_25 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node18_21 node21_25
private theorem node12_25 :
    CellBound source20 nn0 nn1 Qcell ((843:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node12_18 node18_25
private theorem node0_25 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_25
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_25
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24]
theorem packet_count : packets.length = 25 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC02
#check @N11Formalization.C450Source20GroupedC02.bound
#print axioms N11Formalization.C450Source20GroupedC02.valid0
#print axioms N11Formalization.C450Source20GroupedC02.valid1
#print axioms N11Formalization.C450Source20GroupedC02.valid2
#print axioms N11Formalization.C450Source20GroupedC02.valid3
#print axioms N11Formalization.C450Source20GroupedC02.valid4
#print axioms N11Formalization.C450Source20GroupedC02.valid5
#print axioms N11Formalization.C450Source20GroupedC02.valid6
#print axioms N11Formalization.C450Source20GroupedC02.valid7
#print axioms N11Formalization.C450Source20GroupedC02.valid8
#print axioms N11Formalization.C450Source20GroupedC02.valid9
#print axioms N11Formalization.C450Source20GroupedC02.valid10
#print axioms N11Formalization.C450Source20GroupedC02.valid11
#print axioms N11Formalization.C450Source20GroupedC02.valid12
#print axioms N11Formalization.C450Source20GroupedC02.valid13
#print axioms N11Formalization.C450Source20GroupedC02.valid14
#print axioms N11Formalization.C450Source20GroupedC02.valid15
#print axioms N11Formalization.C450Source20GroupedC02.valid16
#print axioms N11Formalization.C450Source20GroupedC02.valid17
#print axioms N11Formalization.C450Source20GroupedC02.valid18
#print axioms N11Formalization.C450Source20GroupedC02.valid19
#print axioms N11Formalization.C450Source20GroupedC02.valid20
#print axioms N11Formalization.C450Source20GroupedC02.valid21
#print axioms N11Formalization.C450Source20GroupedC02.valid22
#print axioms N11Formalization.C450Source20GroupedC02.valid23
#print axioms N11Formalization.C450Source20GroupedC02.valid24
#print axioms N11Formalization.C450Source20GroupedC02.bound
#print axioms N11Formalization.C450Source20GroupedC02.endpoint_checks
