import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6608593333:ℚ)/10000000000),((851087519:ℚ)/1250000000),((-5819787671:ℚ)/12400000000),((-4688593333:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1291256009:ℚ)/2500000000),((93866152402738146864005299754620007689138489043206146793:ℚ)/391043631115722656250000000000000000000000000000000000000),((560543014603163078870871153:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6728317281:ℚ)/10000000000),((866047571:ℚ)/1250000000),((-5954428139:ℚ)/12637500000),((-4808317281:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4836470297:ℚ)/10000000000),((1078484101160646742321665994166255660881272880764214427787:ℚ)/4495227038574218750000000000000000000000000000000000000000),((547367008539792100096386297:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((684800487:ℚ)/1000000000),((55905663:ℚ)/80000000),((-385390967:ℚ)/824000000),((-164266829:ℚ)/433125000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((448604379:ℚ)/1000000000),((3092176862206571924683207955562218663790813839294537:ℚ)/13076665256881713867187500000000000000000000000000000),((5340792501620951805052713:ℚ)/29573120000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6907835663:ℚ)/10000000000),((7048026897:ℚ)/10000000000),((-4428385643:ℚ)/9450000000),((-4987835663:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4300959541:ℚ)/10000000000),((52476494875528543499246375575118156156290547573014254419:ℚ)/221930544699096679687500000000000000000000000000000000000),((527393425915921409384127513:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3483829053:ℚ)/5000000000),((7107837861:ℚ)/10000000000),((-49250540749:ℚ)/104900000000),((-2523829053:ℚ)/6615625000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((821622651:ℚ)/2000000000),((448846950314564392182428254120167462578691191927620744303:ℚ)/1898314410788917541503906250000000000000000000000000000000),((130169904832508147684196993:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((7027472429:ℚ)/10000000000),((3583820493:ℚ)/5000000000),((-24894384437:ℚ)/52925000000),((-5107472429:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3906350761:ℚ)/10000000000),((620265680186540286283872184159890367120392221809879119361:ℚ)/2623393429101562500000000000000000000000000000000000000000),((513937816532224880289695457:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((7087278851:ℚ)/10000000000),((22585739:ℚ)/31250000),((-157271651:ℚ)/333750000),((-5167278851:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((738841301:ℚ)/2000000000),((1255197548665376640644580724294994110917292944483812049:ℚ)/5308990328758955001831054687500000000000000000000000000),((507168004451878458846795777:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7147077583:ℚ)/10000000000),((1821806137:ℚ)/2500000000),((-12716255233:ℚ)/26937500000),((-5227077583:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((346977159:ℚ)/1000000000),((1597582905743081847848457278183113762388717049852446065427:ℚ)/6757342917395019531250000000000000000000000000000000000000),((500370170504917985251392153:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7206868831:ℚ)/10000000000),((918375673:ℚ)/1250000000),((-6425381057:ℚ)/13587500000),((-5286868831:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((32304799:ℚ)/100000000),((114878585585695937506143544371141339465850400660575454923:ℚ)/485918023128890991210937500000000000000000000000000000000),((493544302270063600152133497:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((908331599:ℚ)/1250000000),((3703389589:ℚ)/5000000000),((-25970506301:ℚ)/54825000000),((-668331599:ℚ)/1728125000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2972740049:ℚ)/10000000000),((87098117159781927074674888344517949046399350750264551:ℚ)/368419729432463645935058593750000000000000000000000000),((7604537311884066839053977:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((915803707:ℚ)/1250000000),((7526306363:ℚ)/10000000000),((-53016757267:ℚ)/110600000000),((-675803707:ℚ)/1757812500),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1345625289:ℚ)/5000000000),((17557794778889615405394766378990588256034503545719709:ℚ)/73330193117726594209671020507812500000000000000000000),((7497006503365550003117073:ℚ)/46208000000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((372298141:ℚ)/500000000),((7645807487:ℚ)/10000000000),((-54092267383:ℚ)/112500000000),((-276298141:ℚ)/715000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1008387033:ℚ)/5000000000),((1640461284118399891302069030808348538602611139533733:ℚ)/6853610156250000000000000000000000000000000000000000),((3226871585674207861017:ℚ)/20480000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((3782734861:ℚ)/5000000000),((4061788003:ℚ)/5000000000),((-29196092027:ℚ)/57200000000),((-2822734861:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((476807211:ℚ)/5000000000),((101448998584330512871078583291972146903296032775414901073:ℚ)/396219274902343750000000000000000000000000000000000000000),((112999935143621764971034017:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((8043259521:ℚ)/10000000000),((2150254327:ℚ)/2500000000),((-15672288943:ℚ)/30500000000),((-680362169:ℚ)/1800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((62862818653130005008589651871357769942271600224994231:ℚ)/247050000000000000000000000000000000000000000000000000),((155105439:ℚ)/1024000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((532544973:ℚ)/625000000),((10508450233:ℚ)/10000000000),((-79856052097:ℚ)/129600000000),((-412544973:ℚ)/1250000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((100392653586972452367566725878941258675611119241952509:ℚ)/329589843750000000000000000000000000000000000000000000),((155105439:ℚ)/1024000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((5214104733:ℚ)/5000000000),((7158577503:ℚ)/5000000000),((-57067197527:ℚ)/80000000000),((-1418034911:ℚ)/4600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((152067506933868602216018358070570402513638691877556629605717:ℚ)/423200000000000000000000000000000000000000000000000000000000),((155105439:ℚ)/1024000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC08
#check @N11Formalization.C450Source25GroupedC08.bound
#print axioms N11Formalization.C450Source25GroupedC08.valid0
#print axioms N11Formalization.C450Source25GroupedC08.valid1
#print axioms N11Formalization.C450Source25GroupedC08.valid2
#print axioms N11Formalization.C450Source25GroupedC08.valid3
#print axioms N11Formalization.C450Source25GroupedC08.valid4
#print axioms N11Formalization.C450Source25GroupedC08.valid5
#print axioms N11Formalization.C450Source25GroupedC08.valid6
#print axioms N11Formalization.C450Source25GroupedC08.valid7
#print axioms N11Formalization.C450Source25GroupedC08.valid8
#print axioms N11Formalization.C450Source25GroupedC08.valid9
#print axioms N11Formalization.C450Source25GroupedC08.valid10
#print axioms N11Formalization.C450Source25GroupedC08.valid11
#print axioms N11Formalization.C450Source25GroupedC08.valid12
#print axioms N11Formalization.C450Source25GroupedC08.valid13
#print axioms N11Formalization.C450Source25GroupedC08.valid14
#print axioms N11Formalization.C450Source25GroupedC08.valid15
#print axioms N11Formalization.C450Source25GroupedC08.bound
#print axioms N11Formalization.C450Source25GroupedC08.endpoint_checks
