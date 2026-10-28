import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6353176413:ℚ)/10000000000),((265306063:ℚ)/400000000),((-247386063:ℚ)/396800000),((-52058587717:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5809452353:ℚ)/10000000000),((93832334387482168564663025613665491209621281595193031:ℚ)/4142566198476800000000000000000000000000000000000000000),((174695491324709539511367:ℚ)/1245184000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((6590836029:ℚ)/10000000000),((429395263:ℚ)/625000000),((-401395263:ℚ)/643750000),((-54197524261:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((208485649:ℚ)/400000000),((672526167188752646181496023610802430020249822941943731:ℚ)/29716268578720092773437500000000000000000000000000000000),((8100883991711948986862373:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1707121069:ℚ)/2500000000),((6989155993:ℚ)/10000000000),((-2180385331:ℚ)/3560000000),((-14084089621:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((908981203:ℚ)/2000000000),((7254394147643381656087095768249775528508962386267310014603:ℚ)/333187806544400000000000000000000000000000000000000000000000),((2071349478016829399025149333:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((694730451:ℚ)/1000000000),((3524285411:ℚ)/5000000000),((-3300285411:ℚ)/5435000000),((-337680827:ℚ)/645000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((417466637:ℚ)/1000000000),((9910974533748522484301667197261374839327594373553298323:ℚ)/463826526376367187500000000000000000000000000000000000000),((517530821003292302787230157:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7006713713:ℚ)/10000000000),((3553992483:ℚ)/5000000000),((-3329992483:ℚ)/5482500000),((-57940423417:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3977470009:ℚ)/10000000000),((631215009182616914414238474502708812699567835808731646809:ℚ)/29528234243574032592773437500000000000000000000000000000000),((517499315311273819073006413:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((883265291:ℚ)/1250000000),((3568845893:ℚ)/5000000000),((-3344845893:ℚ)/5530000000),((-7309387619:ℚ)/13884375000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((377055081:ℚ)/1000000000),((110487398932038264539215216816939355129211070191670378112941:ℚ)/5216125673377926562500000000000000000000000000000000000000000),((517347819316857125825623133:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7095826419:ℚ)/10000000000),((3583699221:ℚ)/5000000000),((-3359699221:ℚ)/5553750000),((-58742437771:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3662932071:ℚ)/10000000000),((7056500920799380691933792084999433322517446658883489869273:ℚ)/333056684165447866058349609375000000000000000000000000000000),((517333334072632021989004797:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((712553037:ℚ)/1000000000),((1439420987:ℚ)/2000000000),((-58687869:ℚ)/97000000),((-5900977333:ℚ)/11202500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3552206061:ℚ)/10000000000),((97091229702569689878796698756035407253494386528056437:ℚ)/4581472660488250000000000000000000000000000000000000000),((82771096891653533886017373:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((357761709:ℚ)/500000000),((1806702817:ℚ)/2500000000),((-1694702817:ℚ)/2800625000),((-2963855381:ℚ)/5625000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((859518019:ℚ)/2500000000),((3683203056123546128620880678402774456566740927540979:ℚ)/173760055254006385803222656250000000000000000000000000),((129326470956542114456619813:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7184937853:ℚ)/10000000000),((3628258721:ℚ)/5000000000),((-378250969:ℚ)/625000000),((-59544440677:ℚ)/112975000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1660089069:ℚ)/5000000000),((660660729236587665088549995861897887572094564583151531817:ℚ)/31160523986816406250000000000000000000000000000000000000000),((517292918810230713096837797:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((721464139:ℚ)/1000000000),((364311173:ℚ)/500000000),((-341911173:ℚ)/564875000),((-5981177251:ℚ)/11345000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((1599053959:ℚ)/5000000000),((307478748197494599353688606613752728715633885785481881:ℚ)/14499268117040759246826171875000000000000000000000000000),((5172804605248413099267293:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((905543099:ℚ)/1250000000),((7315929323:ℚ)/10000000000),((-6867929323:ℚ)/11345000000),((-7509887891:ℚ)/14240625000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3071362939:ℚ)/10000000000),((4019880922745418667838711895768146457502203522548546710843099:ℚ)/189518484637218860156250000000000000000000000000000000000000000),((2069074035846489944451908093:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((3637024031:ℚ)/5000000000),((3672817517:ℚ)/5000000000),((-1149605839:ℚ)/1898750000),((-30173216279:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((2939337939:ℚ)/10000000000),((46057669941341203872624305039102886815698597905335239:ℚ)/2170952927209472656250000000000000000000000000000000000),((517257064111510511109186413:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((9129689:ℚ)/12500000),((1851261501:ℚ)/2500000000),((-1739261501:ℚ)/2860000000),((-75767201:ℚ)/144187500),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((700321467:ℚ)/2500000000),((72322351896611260995908224939067260145527139652178453:ℚ)/3377464796341796875000000000000000000000000000000000000),((129343048051380528232789517:ℚ)/924160000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((736315709:ℚ)/1000000000),((7464456387:ℚ)/10000000000),((-7016456387:ℚ)/11535000000),((-6114841381:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1251534271:ℚ)/5000000000),((92634508966366979331108756054566064528900606223369377294857:ℚ)/4324849396020850781250000000000000000000000000000000000000000),((2069411392882966568420290573:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((1855640619:ℚ)/2500000000),((1895818861:ℚ)/2500000000),((-1783818861:ℚ)/2907500000),((-15420765571:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((270638481:ℚ)/1250000000),((32491943108203336762228243173264879615149235765844664093:ℚ)/1490430222737377929687500000000000000000000000000000000000),((129398307649944362209902957:ℚ)/924160000000000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((377068589:ℚ)/500000000),((7820907101:ℚ)/10000000000),((-7372907101:ℚ)/11820000000),((-3137617301:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1242914173:ℚ)/10000000000),((2595575146540735046137902959593275938069851616853493003031:ℚ)/115216153378650000000000000000000000000000000000000000000000),((170105317161263:ℚ)/1216000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7778984843:ℚ)/10000000000),((4148073617:ℚ)/5000000000),((-3924073617:ℚ)/6100000000),((-64890863587:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((222080490639296848566090595183829155653386490877340431681:ℚ)/9307639631250000000000000000000000000000000000000000000000),((143171951:ℚ)/1024000000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((1650838213:ℚ)/2000000000),((2549219879:ℚ)/2500000000),((-2437219879:ℚ)/3240000000),((-13833543917:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((19741313625244654047690414048684373293368139491096909:ℚ)/637729200000000000000000000000000000000000000000000000),((143171951:ℚ)/1024000000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10154819951:ℚ)/10000000000),((3499434737:ℚ)/2500000000),((-3387434737:ℚ)/4000000000),((-86273379559:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((18130940963272605462421583988869261862663736311750362921:ℚ)/476100000000000000000000000000000000000000000000000000000),((143171951:ℚ)/1024000000)⟩
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
end N11Formalization.C450NinthGroupedC07
#check @N11Formalization.C450NinthGroupedC07.bound
#print axioms N11Formalization.C450NinthGroupedC07.valid0
#print axioms N11Formalization.C450NinthGroupedC07.valid1
#print axioms N11Formalization.C450NinthGroupedC07.valid2
#print axioms N11Formalization.C450NinthGroupedC07.valid3
#print axioms N11Formalization.C450NinthGroupedC07.valid4
#print axioms N11Formalization.C450NinthGroupedC07.valid5
#print axioms N11Formalization.C450NinthGroupedC07.valid6
#print axioms N11Formalization.C450NinthGroupedC07.valid7
#print axioms N11Formalization.C450NinthGroupedC07.valid8
#print axioms N11Formalization.C450NinthGroupedC07.valid9
#print axioms N11Formalization.C450NinthGroupedC07.valid10
#print axioms N11Formalization.C450NinthGroupedC07.valid11
#print axioms N11Formalization.C450NinthGroupedC07.valid12
#print axioms N11Formalization.C450NinthGroupedC07.valid13
#print axioms N11Formalization.C450NinthGroupedC07.valid14
#print axioms N11Formalization.C450NinthGroupedC07.valid15
#print axioms N11Formalization.C450NinthGroupedC07.valid16
#print axioms N11Formalization.C450NinthGroupedC07.valid17
#print axioms N11Formalization.C450NinthGroupedC07.valid18
#print axioms N11Formalization.C450NinthGroupedC07.valid19
#print axioms N11Formalization.C450NinthGroupedC07.bound
#print axioms N11Formalization.C450NinthGroupedC07.endpoint_checks
