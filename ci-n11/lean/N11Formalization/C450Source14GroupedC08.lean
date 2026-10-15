import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6426048817:ℚ)/10000000000),((6715627161:ℚ)/10000000000),((-52760644449:ℚ)/99200000000),((-5386048817:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2816170827:ℚ)/5000000000),((59688037329854533584698663851205386743905943696826931771:ℚ)/1240522595214843750000000000000000000000000000000000000000),((2684982362168335772965813179:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((3332032309:ℚ)/5000000000),((854329757:ℚ)/1250000000),((-6728967813:ℚ)/12875000000),((-2812032309:ℚ)/6556250000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5015246053:ℚ)/10000000000),((2112592881523290374499415519024582813172427934471953717:ℚ)/45354853380966186523437500000000000000000000000000000000),((666398034071618375910391491:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((6783058461:ℚ)/10000000000),((3476819819:ℚ)/5000000000),((-27451378371:ℚ)/52450000000),((-5743058461:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((233960743:ℚ)/500000000),((181609060502303397739026373547744933271029305810255758491:ℚ)/3899772849023437500000000000000000000000000000000000000000),((2655889213827987884440346931:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((6902043603:ℚ)/10000000000),((1753284273:ℚ)/2500000000),((-4619852819:ℚ)/8900000000),((-5862043603:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4319201217:ℚ)/10000000000),((730479843130550778863266221930512209087377169453718351:ℚ)/15926970986276865005493164062500000000000000000000000000),((2646181032167477817330260499:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1392306611:ℚ)/2000000000),((7072632399:ℚ)/10000000000),((-55973691591:ℚ)/107750000000),((-1184306611:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2064123779:ℚ)/5000000000),((2479546910880752732679586356573321210930706642155656379:ℚ)/54058743339160156250000000000000000000000000000000000000),((105652998311977752855691731:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7021020501:ℚ)/10000000000),((1426425123:ℚ)/2000000000),((-11301826107:ℚ)/21740000000),((-5981020501:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3928585709:ℚ)/10000000000),((66867929766958958021072893442885499184605803892692414911:ℚ)/1457754069386672973632812500000000000000000000000000000000),((2636467555292588902342190211:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-9:ℚ)/16),((-1:ℚ)/2),((885063249:ℚ)/1250000000),((223808483:ℚ)/312500000),((-591425449:ℚ)/1142187500),((-755063249:ℚ)/1720703125),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3718809253:ℚ)/10000000000),((1059916510468658193487883153959673765852668679358219421:ℚ)/23276369169866666197776794433593750000000000000000000000),((41118887822367985725785211:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7110248021:ℚ)/10000000000),((3595808397:ℚ)/5000000000),((-28522275573:ℚ)/55062500000),((-6070248021:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3609579023:ℚ)/10000000000),((10352820820552177761445876285782573371259970450317877131:ℚ)/227337652796936035156250000000000000000000000000000000000),((2629178952430840973692818051:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((7139989581:ℚ)/10000000000),((1805340409:ℚ)/2500000000),((-14328063681:ℚ)/27650000000),((-6099989581:ℚ)/13884375000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3497094177:ℚ)/10000000000),((315982067672662093168791664687300015918978845676138331281:ℚ)/6938177668729448318481445312500000000000000000000000000000),((2626748749632413736361852371:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7169730677:ℚ)/10000000000),((1812776497:ℚ)/2500000000),((-4798329491:ℚ)/9256250000),((-6129730677:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3381029353:ℚ)/10000000000),((71433080243965622181702393708366974960448368978339850123:ℚ)/1568389247042751312255859375000000000000000000000000000000),((2624318211845263497911908419:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((1439894263:ℚ)/2000000000),((7280849857:ℚ)/10000000000),((-57847648713:ℚ)/111550000000),((-1231894263:ℚ)/2800625000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3261001759:ℚ)/10000000000),((558055396673223700843784291587867897976496777689391807:ℚ)/12251928755253356933593750000000000000000000000000000000),((104875493543855653127419659:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((7229211501:ℚ)/10000000000),((7310593249:ℚ)/10000000000),((-58115339241:ℚ)/112025000000),((-6189211501:ℚ)/14062500000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((392069489:ℚ)/1250000000),((41574102175563156698640280717984558984771787073793468937:ℚ)/912691187113523483276367187500000000000000000000000000000),((2619456129412497117428792211:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7258951241:ℚ)/10000000000),((230314957:ℚ)/312500000),((-610944871:ℚ)/1171875000),((-6218951241:ℚ)/14181250000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1503571367:ℚ)/5000000000),((2044407894374155748044899843119560008215587739046671:ℚ)/44561886249542236328125000000000000000000000000000000),((2617024583819979587800766091:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((3659214703:ℚ)/5000000000),((7429562161:ℚ)/10000000000),((-59186059449:ℚ)/113450000000),((-3139214703:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2730561053:ℚ)/10000000000),((237818227170635113775413737740513720488243991363957247957:ℚ)/5183613814843750000000000000000000000000000000000000000000),((653040120398738963438703099:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7377905853:ℚ)/10000000000),((7548523901:ℚ)/10000000000),((-60256715109:ℚ)/114400000000),((-6337905853:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((302935449:ℚ)/1250000000),((127701664476139163514100293205939488077232667776727566141:ℚ)/2745903293713378906250000000000000000000000000000000000000),((2607295028535648389224256499:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((3748426881:ℚ)/5000000000),((239608713:ℚ)/312500000),((-1916478417:ℚ)/3634375000),((-3228426881:ℚ)/7387500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((329881001:ℚ)/2000000000),((1261541210173310011216646758157697557116839799373474111:ℚ)/27134914547729492187500000000000000000000000000000000000),((649390014148878799612930971:ℚ)/3696640000000000000000000000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((3807897647:ℚ)/5000000000),((1976342363:ℚ)/2500000000),((-5289027089:ℚ)/9850000000),((-3287897647:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((78029976701866200608266086271773794343785755535095599407:ℚ)/1637521618652343750000000000000000000000000000000000000000),((179301489:ℚ)/1024000000)⟩
theorem valid16 : Valid source14 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((3926830209:ℚ)/5000000000),((8381081847:ℚ)/10000000000),((-67749736623:ℚ)/122000000000),((-3406830209:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3359555890456295920551017636348831431272185093759132657:ℚ)/67537293750000000000000000000000000000000000000000000000),((179301489:ℚ)/1024000000)⟩
theorem valid17 : Valid source14 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((4164663149:ℚ)/5000000000),((514162677:ℚ)/500000000),((-1414488031:ℚ)/2160000000),((-3644663149:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((11479277722979293380356413891178625774151341716643067:ℚ)/188956800000000000000000000000000000000000000000000000),((179301489:ℚ)/1024000000)⟩
theorem valid18 : Valid source14 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((5115678131:ℚ)/5000000000),((14085801139:ℚ)/10000000000),((-119092210251:ℚ)/160000000000),((-4595678131:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((739668552738351558617417516252035228546570156987862589731863:ℚ)/10156800000000000000000000000000000000000000000000000000000000),((179301489:ℚ)/1024000000)⟩
theorem valid19 : Valid source14 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet19 valid19
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
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((881:ℚ)/1280) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC08
#check @N11Formalization.C450Source14GroupedC08.bound
#print axioms N11Formalization.C450Source14GroupedC08.valid0
#print axioms N11Formalization.C450Source14GroupedC08.valid1
#print axioms N11Formalization.C450Source14GroupedC08.valid2
#print axioms N11Formalization.C450Source14GroupedC08.valid3
#print axioms N11Formalization.C450Source14GroupedC08.valid4
#print axioms N11Formalization.C450Source14GroupedC08.valid5
#print axioms N11Formalization.C450Source14GroupedC08.valid6
#print axioms N11Formalization.C450Source14GroupedC08.valid7
#print axioms N11Formalization.C450Source14GroupedC08.valid8
#print axioms N11Formalization.C450Source14GroupedC08.valid9
#print axioms N11Formalization.C450Source14GroupedC08.valid10
#print axioms N11Formalization.C450Source14GroupedC08.valid11
#print axioms N11Formalization.C450Source14GroupedC08.valid12
#print axioms N11Formalization.C450Source14GroupedC08.valid13
#print axioms N11Formalization.C450Source14GroupedC08.valid14
#print axioms N11Formalization.C450Source14GroupedC08.valid15
#print axioms N11Formalization.C450Source14GroupedC08.valid16
#print axioms N11Formalization.C450Source14GroupedC08.valid17
#print axioms N11Formalization.C450Source14GroupedC08.valid18
#print axioms N11Formalization.C450Source14GroupedC08.valid19
#print axioms N11Formalization.C450Source14GroupedC08.bound
#print axioms N11Formalization.C450Source14GroupedC08.endpoint_checks
