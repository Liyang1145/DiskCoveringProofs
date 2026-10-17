import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6335256247:ℚ)/10000000000),((6612060811:ℚ)/10000000000),((-1775114429:ℚ)/3200000000),((-5695256247:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1463069161:ℚ)/2500000000),((296457683942201134796007207962914538218075287505429231:ℚ)/13338952636718750000000000000000000000000000000000000000),((1738877262207782947990743:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((3286465693:ℚ)/5000000000),((53513707:ℚ)/78125000),((-446623363:ℚ)/804687500),((-2966465693:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5259261089:ℚ)/10000000000),((1288743856777687610020982568074698576347508567483457831:ℚ)/58039587067812681198120117187500000000000000000000000000),((216924297366465378667341:ℚ)/1805000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6810594049:ℚ)/10000000000),((3484298127:ℚ)/5000000000),((-29118683143:ℚ)/53400000000),((-6170594049:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((919647201:ℚ)/2000000000),((8064766456138159677049799410247079380572334642545126930540477:ℚ)/374836282362450000000000000000000000000000000000000000000000000),((324397717626896511814699:ℚ)/2707500000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6929421111:ℚ)/10000000000),((7028015939:ℚ)/10000000000),((-58772143451:ℚ)/108700000000),((-6289421111:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((169293147:ℚ)/400000000),((1336730754196989075643996475466235648770312200714951018364011:ℚ)/63080407587185937500000000000000000000000000000000000000000000),((1727496838772302607732743:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((174720841:ℚ)/250000000),((885929357:ℚ)/1250000000),((-7413364213:ℚ)/13706250000),((-158720841:ℚ)/345625000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2018887813:ℚ)/5000000000),((4890089587083344476482141928573251962868429738040872220127:ℚ)/230689330027922129631042480468750000000000000000000000000000),((53958465245414974471859:ℚ)/451250000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((1762061381:ℚ)/2500000000),((222410751:ℚ)/312500000),((-1861696759:ℚ)/3456250000),((-1602061381:ℚ)/3471093750),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3833930869:ℚ)/10000000000),((26795968220714239352334852860740685468448124695235385532727:ℚ)/1273468181977032852172851562500000000000000000000000000000000),((17026636865532591971269:ℚ)/142500000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7077951229:ℚ)/10000000000),((7146853023:ℚ)/10000000000),((-59841677207:ℚ)/111075000000),((-279910923:ℚ)/606250000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3728049333:ℚ)/10000000000),((106002913520213381075969253861388083531295471298866932652231:ℚ)/5036774051651385498046875000000000000000000000000000000000000),((5174873929546816219624021:ℚ)/43320000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((3553828389:ℚ)/5000000000),((7176561833:ℚ)/10000000000),((-2613437239:ℚ)/4850000000),((-3233828389:ℚ)/7001562500),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3619220773:ℚ)/10000000000),((12054857483548110627429860852616518648610711627010313609367:ℚ)/572684082561031250000000000000000000000000000000000000000000),((1724552115151514976057387:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((285494487:ℚ)/400000000),((7206270461:ℚ)/10000000000),((-60376434149:ℚ)/112025000000),((-259894487:ℚ)/562500000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3507170343:ℚ)/10000000000),((58532386627320473676222756285236650835640805397635334773:ℚ)/2780160884064102172851562500000000000000000000000000000000),((1724148284774175405119143:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((358353371:ℚ)/500000000),((7235978913:ℚ)/10000000000),((-60643810217:ℚ)/112500000000),((-326353371:ℚ)/706093750),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3391578217:ℚ)/10000000000),((1275570293918579450406446912712923787830970074556309978523247923:ℚ)/60576058630371093750000000000000000000000000000000000000000000000),((5171239456338350933001481:ℚ)/43320000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((1799193129:ℚ)/2500000000),((1816421797:ℚ)/2500000000),((-15227796173:ℚ)/28243750000),((-1639193129:ℚ)/3545312500),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3272068523:ℚ)/10000000000),((38171070826029602449726105804136351275072708704097770579381:ℚ)/1812408514630094905853271484375000000000000000000000000000000),((26927292453502666404893:ℚ)/225625000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((1445295493:ℚ)/2000000000),((729539529:ℚ)/1000000000),((-6117855761:ℚ)/11345000000),((-42493403:ℚ)/91875000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3148194591:ℚ)/10000000000),((4154120875207422943372644771824318792724784508095062708937:ℚ)/197209661433110156250000000000000000000000000000000000000000),((12922117346091741432871:ℚ)/108300000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7256182267:ℚ)/10000000000),((7325103221:ℚ)/10000000000),((-61445928989:ℚ)/113925000000),((-6616182267:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((754854691:ℚ)/2500000000),((9879288267134003877272395601166557486308691310461034213439:ℚ)/468925832277246093750000000000000000000000000000000000000000),((1722553272808535026729703:ℚ)/14440000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3642943463:ℚ)/5000000000),((7384518577:ℚ)/10000000000),((-61980667193:ℚ)/114400000000),((-1107647821:ℚ)/2403125000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((72127103:ℚ)/250000000),((13764353448228885592503865820826549859145073980587496533963:ℚ)/648473240897625000000000000000000000000000000000000000000000),((1722663001455820139841707:ℚ)/14440000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((367264791:ℚ)/500000000),((7443933273:ℚ)/10000000000),((-62515399457:ℚ)/115350000000),((-335264791:ℚ)/726875000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((259625091:ℚ)/1000000000),((91817774149474847160947515174283411198405655895330813354640267:ℚ)/4324849396020850781250000000000000000000000000000000000000000000),((5165657383794883678982521:ℚ)/43320000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((46279401:ℚ)/62500000),((30251043:ℚ)/40000000),((-254339387:ℚ)/465200000),((-42279401:ℚ)/92343750),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2271899469:ℚ)/10000000000),((131461759645405449502220691500591906436236942934357659:ℚ)/6104802192332300000000000000000000000000000000000000000),((82662998893525471201:ℚ)/693120000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((752351923:ℚ)/1000000000),((975051057:ℚ)/1250000000),((-8215459513:ℚ)/14775000000),((-688351923:ℚ)/1525000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((354968007:ℚ)/2500000000),((4976054702802999432533023929345860779688692313477679761507:ℚ)/225031549567675781250000000000000000000000000000000000000000),((1158207906094461:ℚ)/9728000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((1940285821:ℚ)/2500000000),((4137838931:ℚ)/5000000000),((-35000550379:ℚ)/61000000000),((-593428607:ℚ)/1350000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((23958422780424572612819062295687816666090975677286167786027:ℚ)/1034182181250000000000000000000000000000000000000000000000000),((304383:ℚ)/2560000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((4118184777:ℚ)/5000000000),((1017649939:ℚ)/1000000000),((-8710849451:ℚ)/12960000000),((-3798184777:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1170987440897126079553798033210966292313014613617134081:ℚ)/40814668800000000000000000000000000000000000000000000000),((304383:ℚ)/2560000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((2027411913:ℚ)/2000000000),((6988731769:ℚ)/5000000000),((-60658585921:ℚ)/80000000000),((-1899411913:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((131304014707661988116656638922541938465263344317395749127577:ℚ)/3808800000000000000000000000000000000000000000000000000000000),((304383:ℚ)/2560000)⟩
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
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((4519:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
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
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC08
#check @N11Formalization.C450NinthGroupedC08.bound
#print axioms N11Formalization.C450NinthGroupedC08.valid0
#print axioms N11Formalization.C450NinthGroupedC08.valid1
#print axioms N11Formalization.C450NinthGroupedC08.valid2
#print axioms N11Formalization.C450NinthGroupedC08.valid3
#print axioms N11Formalization.C450NinthGroupedC08.valid4
#print axioms N11Formalization.C450NinthGroupedC08.valid5
#print axioms N11Formalization.C450NinthGroupedC08.valid6
#print axioms N11Formalization.C450NinthGroupedC08.valid7
#print axioms N11Formalization.C450NinthGroupedC08.valid8
#print axioms N11Formalization.C450NinthGroupedC08.valid9
#print axioms N11Formalization.C450NinthGroupedC08.valid10
#print axioms N11Formalization.C450NinthGroupedC08.valid11
#print axioms N11Formalization.C450NinthGroupedC08.valid12
#print axioms N11Formalization.C450NinthGroupedC08.valid13
#print axioms N11Formalization.C450NinthGroupedC08.valid14
#print axioms N11Formalization.C450NinthGroupedC08.valid15
#print axioms N11Formalization.C450NinthGroupedC08.valid16
#print axioms N11Formalization.C450NinthGroupedC08.valid17
#print axioms N11Formalization.C450NinthGroupedC08.valid18
#print axioms N11Formalization.C450NinthGroupedC08.valid19
#print axioms N11Formalization.C450NinthGroupedC08.bound
#print axioms N11Formalization.C450NinthGroupedC08.endpoint_checks
