import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((3056126611:ℚ)/5000000000),((6616831397:ℚ)/10000000000),((11408379833:ℚ)/53400000000),((7896831397:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((795492879:ℚ)/1250000000),((4084573847531120236067692685972923115233:ℚ)/271842636672000000000000000000000000000000),((-769449182016294124956287:ℚ)/10240000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6587805109:ℚ)/10000000000),((1713631579:ℚ)/2500000000),((24243415327:ℚ)/110600000000),((677877193:ℚ)/2225000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((652518107:ℚ)/1250000000),((875597876569487692442177261546771330325629743642719090373:ℚ)/63159921363574218750000000000000000000000000000000000000000),((-1149862315100182312492725127:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((1706388141:ℚ)/2500000000),((13619861:ℚ)/19531250),((6239164423:ℚ)/28125000000),((64479444:ℚ)/216015625),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((142302659:ℚ)/312500000),((156043421922860678465182535177775606301769450855041:ℚ)/11663864797353744506835937500000000000000000000000000),((-73084742295715447528703127:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((3472210007:ℚ)/5000000000),((7032788927:ℚ)/10000000000),((12656630021:ℚ)/56725000000),((8312788927:ℚ)/28125000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2092008769:ℚ)/5000000000),((9418354693365447813838128145877475924096797275548522314060609:ℚ)/715857538032531738281250000000000000000000000000000000000000000),((-294782224486633461897907183:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((7003852261:ℚ)/10000000000),((443263017:ℚ)/625000000),((2317414253:ℚ)/10400000000),((523263017:ℚ)/1772656250),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((249198691:ℚ)/625000000),((485878313767782966993238084331626665922950068357794771:ℚ)/37075489359619140625000000000000000000000000000000000000),((-1184021975356093946221975207:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((1765820889:ℚ)/2500000000),((1430325377:ℚ)/2000000000),((6417462667:ℚ)/28837500000),((153302307:ℚ)/520000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((118146339:ℚ)/312500000),((5088716482082051928585799565123673839583649434395747903:ℚ)/389766035100000000000000000000000000000000000000000000000),((-74307464567879246253854607:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7122713923:ℚ)/10000000000),((1442208957:ℚ)/2000000000),((25848141769:ℚ)/116300000000),((1698208957:ℚ)/5767500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3562846011:ℚ)/10000000000),((281306018661418271598236925371903701204659148922440578433:ℚ)/21624246980104253906250000000000000000000000000000000000000),((-1193821272902622183479537143:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/16),((1:ℚ)/4),((897767923:ℚ)/1250000000),((727046199:ℚ)/1000000000),((3253303769:ℚ)/14656250000),((855046199:ℚ)/2907500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3331440367:ℚ)/10000000000),((328538868074100786676624765101879875271369981148494951251:ℚ)/25342306337978540039062500000000000000000000000000000000000),((-18730117131467851920765143:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((7241571961:ℚ)/10000000000),((1465975703:ℚ)/2000000000),((26204715883:ℚ)/118200000000),((245996529:ℚ)/837500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((770851969:ℚ)/2500000000),((4142477712484929052551820905655020486715457318623747127:ℚ)/320589603890991210937500000000000000000000000000000000000),((-1203638105234819709275133007:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((1825249919:ℚ)/2500000000),((7389294377:ℚ)/10000000000),((6595749757:ℚ)/29787500000),((8669294377:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((703587739:ℚ)/2500000000),((35389054198350963507420496614742815830094590412061595227498237:ℚ)/2747399484402935156250000000000000000000000000000000000000000000),((-75534568811665571827586687:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7360426549:ℚ)/10000000000),((931088699:ℚ)/1250000000),((26561279647:ℚ)/120100000000),((1091088699:ℚ)/3723437500),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2517532273:ℚ)/10000000000),((5976498397814440955275005361200283000763952352833186521663:ℚ)/465369843667142081260681152343750000000000000000000000000000),((-3361419626403863483624047:ℚ)/40960000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((37099263:ℚ)/50000000),((3783769071:ℚ)/5000000000),((133697789:ℚ)/610000000),((4423769071:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2181643659:ℚ)/10000000000),((1015491979150577918523343313455038750612753326781883692337:ℚ)/78686231925305175781250000000000000000000000000000000000000),((-30459906478465608548223:ℚ)/369664000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((1507740463:ℚ)/2000000000),((8042829289:ℚ)/10000000000),((5419221389:ℚ)/25920000000),((9322829289:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1270932751:ℚ)/10000000000),((3895115948725338817730514205260569881845766337576038566503:ℚ)/290863738476562500000000000000000000000000000000000000000000),((-49130279302311338471718623:ℚ)/591462400000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((4007035951:ℚ)/5000000000),((9943717099:ℚ)/10000000000),((14261107853:ℚ)/80000000000),((3741239033:ℚ)/10800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((21905084477460585938279323289905872201084621342080813:ℚ)/1476225000000000000000000000000000000000000000000000000),((-85412029:ℚ)/1024000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((1983039769:ℚ)/2000000000),((2748951803:ℚ)/2000000000),((6845119307:ℚ)/44160000000),((3004951803:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((11069391428479762167124756787855333983:ℚ)/609408000000000000000000000000000000000),((-85412029:ℚ)/1024000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC20
#check @N11Formalization.C450NinthGroupedC20.bound
#print axioms N11Formalization.C450NinthGroupedC20.valid0
#print axioms N11Formalization.C450NinthGroupedC20.valid1
#print axioms N11Formalization.C450NinthGroupedC20.valid2
#print axioms N11Formalization.C450NinthGroupedC20.valid3
#print axioms N11Formalization.C450NinthGroupedC20.valid4
#print axioms N11Formalization.C450NinthGroupedC20.valid5
#print axioms N11Formalization.C450NinthGroupedC20.valid6
#print axioms N11Formalization.C450NinthGroupedC20.valid7
#print axioms N11Formalization.C450NinthGroupedC20.valid8
#print axioms N11Formalization.C450NinthGroupedC20.valid9
#print axioms N11Formalization.C450NinthGroupedC20.valid10
#print axioms N11Formalization.C450NinthGroupedC20.valid11
#print axioms N11Formalization.C450NinthGroupedC20.valid12
#print axioms N11Formalization.C450NinthGroupedC20.valid13
#print axioms N11Formalization.C450NinthGroupedC20.valid14
#print axioms N11Formalization.C450NinthGroupedC20.bound
#print axioms N11Formalization.C450NinthGroupedC20.endpoint_checks
