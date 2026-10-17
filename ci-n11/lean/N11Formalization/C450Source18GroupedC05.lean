import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6622556103:ℚ)/10000000000),((6812721761:ℚ)/10000000000),((-17878165283:ℚ)/24800000000),((-61968117133:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((640962371:ℚ)/1250000000),((3357386263518989125160307817839005451763197970696494655072489:ℚ)/48720010737600000000000000000000000000000000000000000000000000),((4673619280101700979158369:ℚ)/11552000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((674163483:ℚ)/1000000000),((6931768159:ℚ)/10000000000),((-18235304477:ℚ)/25275000000),((-6327798313:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2399325439:ℚ)/5000000000),((110762541993506210788732495058899368178988795644778331822853:ℚ)/1605902664196142578125000000000000000000000000000000000000000),((46757644238552223938249:ℚ)/115520000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((6860701381:ℚ)/10000000000),((6991287279:ℚ)/10000000000),((-18413861837:ℚ)/25750000000),((-7176412799:ℚ)/11550000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4447369507:ℚ)/10000000000),((47616365229390410834664847907776479517203856984222422759439:ℚ)/711779851647949218750000000000000000000000000000000000000000),((4675717184558638577568201:ℚ)/11552000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6920230299:ℚ)/10000000000),((7050803781:ℚ)/10000000000),((-1690219213:ℚ)/2362500000),((-65242533289:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((266354853:ℚ)/625000000),((758914299271168188071663667008791729450990245043849110439:ℚ)/11335911802473449707031250000000000000000000000000000000000),((4676755989563611481644041:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((348987821:ℚ)/500000000),((7110317733:ℚ)/10000000000),((-18770953199:ℚ)/26225000000),((-3294866031:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2034033769:ℚ)/5000000000),((231824720847154097973396792261118831357832516238030187871381:ℚ)/3460312871291845703125000000000000000000000000000000000000000),((11694462809000971642281:ℚ)/28880000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7039279817:ℚ)/10000000000),((285602951:ℚ)/400000000),((-754408853:ℚ)/1058500000),((-66552077987:ℚ)/106325000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((60396023:ℚ)/156250000),((4425170163310505208941545908790054911911101007146222864399:ℚ)/67036815295923639453125000000000000000000000000000000000000),((4677727851436521490808449:ℚ)/11552000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((3534520259:ℚ)/5000000000),((1433965841:ℚ)/2000000000),((-3789897523:ℚ)/5316250000),((-11146574283:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3760108223:ℚ)/10000000000),((30701292012345123567732085738272685480225872304769279343:ℚ)/464896455639737701416015625000000000000000000000000000000),((1169558495268049365596921:ℚ)/2888000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1419760113:ℚ)/2000000000),((7199584031:ℚ)/10000000000),((-19038752093:ℚ)/26700000000),((-13441361243:ℚ)/21455000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((365199011:ℚ)/1000000000),((1130577683302871634497849186286567015843598126141796875769311:ℚ)/17112791573291162109375000000000000000000000000000000000000000),((187149507765569577206929:ℚ)/462080000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((222767499:ℚ)/312500000),((3614669131:ℚ)/5000000000),((-9564007393:ℚ)/13409375000),((-2110442489:ℚ)/3367187500),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((708145339:ℚ)/2000000000),((1084090499972318501493148132062643256233684208709737967113:ℚ)/16402553389838856831192970275878906250000000000000000000000),((9139138654156779986657:ℚ)/22562500000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3579159367:ℚ)/5000000000),((1451818381:ℚ)/2000000000),((-3843455143:ℚ)/5387500000),((-33930753037:ℚ)/54112500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((685202201:ℚ)/2000000000),((37843487626823451802967202831530117471757198761135786935909:ℚ)/572357081039745712280273437500000000000000000000000000000000),((1169934467928168685503649:ℚ)/2888000000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((898509609:ℚ)/1250000000),((911105621:ℚ)/1250000000),((-2413316863:ℚ)/3382031250),((-8523605699:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((132299331:ℚ)/400000000),((170230999719690846811100442595121744515416028193412378923:ℚ)/2573646977266761660575866699218750000000000000000000000000),((73128661511885545114721:ℚ)/180500000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7217834391:ℚ)/10000000000),((3659298729:ℚ)/5000000000),((-9697896187:ℚ)/13587500000),((-68516178301:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3184717321:ℚ)/10000000000),((618252661120103691753212703470136521857189173615363138866201:ℚ)/9343618419663073348999023437500000000000000000000000000000000),((4680728386301395798742721:ℚ)/11552000000000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3623795649:ℚ)/5000000000),((918543673:ℚ)/1250000000),((-2435631019:ℚ)/3411718750),((-34421752139:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((1528601003:ℚ)/5000000000),((316041989885720268633537345615172691790484813167228972170431:ℚ)/4774599396886633479595184326171875000000000000000000000000000),((1170305005168204260897841:ℚ)/2888000000000000000000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((3638673801:ℚ)/5000000000),((740785157:ℚ)/1000000000),((-45729197:ℚ)/63750000),((-34585411811:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1462157737:ℚ)/5000000000),((12477979121793314695859598950233654664713440345211207:ℚ)/185695814479064941406250000000000000000000000000000000),((1170696452724473182650241:ℚ)/2888000000000000000000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7336858431:ℚ)/10000000000),((7467351583:ℚ)/10000000000),((-19842054749:ℚ)/27650000000),((-69825442741:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((263914981:ℚ)/1000000000),((2498311010606659053232858404247584309784601256342647666391:ℚ)/37161176514868164062500000000000000000000000000000000000000),((4683756966759797452586801:ℚ)/11552000000000000000000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((3698183469:ℚ)/5000000000),((3763424739:ℚ)/5000000000),((-10010274217:ℚ)/13943750000),((-35240018159:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2320100767:ℚ)/10000000000),((2884775794151392703981184775683408500349708202201200199:ℚ)/42889780219602584838867187500000000000000000000000000000),((1171179616689190026287001:ℚ)/2888000000000000000000000)⟩
theorem valid15 : Valid source18 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((232996037:ℚ)/312500000),((3822919563:ℚ)/5000000000),((-10188758689:ℚ)/14062500000),((-2222956407:ℚ)/3575000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1950604983:ℚ)/10000000000),((12292644883354033147018053246098897951001260024176545536363:ℚ)/177709114551544189453125000000000000000000000000000000000000),((4576332446222778403529:ℚ)/11281250000000000000000)⟩
theorem valid16 : Valid source18 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((3787439557:ℚ)/5000000000),((8121722869:ℚ)/10000000000),((-21805168607:ℚ)/28600000000),((-36221835127:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((813289897:ℚ)/10000000000),((65304010914390276402801230361482526275023686347304443049487:ℚ)/816073068525000000000000000000000000000000000000000000000000),((1170933378877215363857609:ℚ)/2888000000000000000000000)⟩
theorem valid17 : Valid source18 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((8050822883:ℚ)/10000000000),((8597502707:ℚ)/10000000000),((-23232508121:ℚ)/30500000000),((-77679051713:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((46063282123996704671917743248735946876365874632831036604923:ℚ)/581727476953125000000000000000000000000000000000000000000000),((405403:ℚ)/1000000)⟩
theorem valid18 : Valid source18 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((1065831959:ℚ)/1250000000),((5249939941:ℚ)/5000000000),((-14469819823:ℚ)/16200000000),((-10364151549:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((287739057267157552823900987286897304890151146720734063:ℚ)/2491129687500000000000000000000000000000000000000000000),((405403:ℚ)/1000000)⟩
theorem valid19 : Valid source18 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10429194159:ℚ)/10000000000),((2860533669:ℚ)/2000000000),(-1:ℚ),((-103841135749:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3750753960385271134435658609:ℚ)/24376320000000000000000000000),((405403:ℚ)/1000000)⟩
theorem valid20 : Valid source18 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source18 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source18 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source18 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((4329:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source18 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4329:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((4329:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source18 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC05
#check @N11Formalization.C450Source18GroupedC05.bound
#print axioms N11Formalization.C450Source18GroupedC05.valid0
#print axioms N11Formalization.C450Source18GroupedC05.valid1
#print axioms N11Formalization.C450Source18GroupedC05.valid2
#print axioms N11Formalization.C450Source18GroupedC05.valid3
#print axioms N11Formalization.C450Source18GroupedC05.valid4
#print axioms N11Formalization.C450Source18GroupedC05.valid5
#print axioms N11Formalization.C450Source18GroupedC05.valid6
#print axioms N11Formalization.C450Source18GroupedC05.valid7
#print axioms N11Formalization.C450Source18GroupedC05.valid8
#print axioms N11Formalization.C450Source18GroupedC05.valid9
#print axioms N11Formalization.C450Source18GroupedC05.valid10
#print axioms N11Formalization.C450Source18GroupedC05.valid11
#print axioms N11Formalization.C450Source18GroupedC05.valid12
#print axioms N11Formalization.C450Source18GroupedC05.valid13
#print axioms N11Formalization.C450Source18GroupedC05.valid14
#print axioms N11Formalization.C450Source18GroupedC05.valid15
#print axioms N11Formalization.C450Source18GroupedC05.valid16
#print axioms N11Formalization.C450Source18GroupedC05.valid17
#print axioms N11Formalization.C450Source18GroupedC05.valid18
#print axioms N11Formalization.C450Source18GroupedC05.valid19
#print axioms N11Formalization.C450Source18GroupedC05.valid20
#print axioms N11Formalization.C450Source18GroupedC05.bound
#print axioms N11Formalization.C450Source18GroupedC05.endpoint_checks
