import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5747749589:ℚ)/10000000000),((314330013:ℚ)/500000000),((14584749041:ℚ)/17800000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3565918137:ℚ)/5000000000),((-4194942174611509417144982817317832731:ℚ)/70496900000000000000000000000000000000),((-454505204511060281004403:ℚ)/1848320000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6222909783:ℚ)/10000000000),((52193737:ℚ)/80000000),((47080368481:ℚ)/55300000000),((56289737:ℚ)/56960000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6114719139:ℚ)/10000000000),((-42567352088316522686738880977381084426466577941883963403:ℚ)/634171413750000000000000000000000000000000000000000000000),((-11525887713306390979403:ℚ)/47316992000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((323024081:ℚ)/500000000),((6761826221:ℚ)/10000000000),((2437168567:ℚ)/2860000000),((21821478663:ℚ)/22120000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5546907233:ℚ)/10000000000),((-1965049209582177755141131586915975593375042675318567:ℚ)/29242070000000000000000000000000000000000000000000000),((-178380992585682154707936467:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3349024341:ℚ)/5000000000),((3440314047:ℚ)/5000000000),((25203170387:ℚ)/29075000000),((11088942141:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((984286369:ℚ)/2000000000),((-2171300650807296469701168843740875467938765969237994443:ℚ)/30723393496093750000000000000000000000000000000000000000),((-44381286421653861391665883:ℚ)/184832000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((681683057:ℚ)/1000000000),((6940028399:ℚ)/10000000000),((5123781399:ℚ)/5862500000),((22356085197:ℚ)/23260000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((915942147:ℚ)/2000000000),((-18227838105202387370173110608408288570124940463231319:ℚ)/251859641113281250000000000000000000000000000000000000),((-177097135615522092467929787:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((55009769:ℚ)/80000000),((3499714149:ℚ)/5000000000),((413228383:ℚ)/472800000),((11267142447:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2199832433:ℚ)/5000000000),((-796420713364877631567574189195243683368297880061:ℚ)/11009337120000000000000000000000000000000000000000),((-44167266922584844149546787:ℚ)/184832000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6935611431:ℚ)/10000000000),((7058827799:ℚ)/10000000000),((52069280017:ℚ)/59575000000),((7570827799:ℚ)/7880000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4212452927:ℚ)/10000000000),((-57334800403254924007361837118438995235836281292926462859:ℚ)/792909134003906250000000000000000000000000000000000000000),((-176240941854648960696754187:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6995001493:ℚ)/10000000000),((222444591:ℚ)/312500000),((52485010451:ℚ)/60050000000),((715333773:ℚ)/744687500),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2008534771:ℚ)/5000000000),((-14673280613144958522809333624534664200562107375829119137:ℚ)/203006671992187500000000000000000000000000000000000000000),((-171692146521075736588747:ℚ)/722000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1763597829:ℚ)/2500000000),((7177625647:ℚ)/10000000000),((13225184803:ℚ)/15131250000),((23068876941:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3812254777:ℚ)/10000000000),((-234662106636376669014317070777563395999032741721401449:ℚ)/3247848005905151367187500000000000000000000000000000000),((-175384516168226930531770683:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((7113780907:ℚ)/10000000000),((1809256003:ℚ)/2500000000),((53316466349:ℚ)/61000000000),((645752001:ℚ)/672500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((35963937:ℚ)/100000000),((-61476133321538206499789405152015476557175501378962941303:ℚ)/851178750000000000000000000000000000000000000000000000000),((-10934763511878513870354483:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((717317027:ℚ)/1000000000),((1459284403:ℚ)/2000000000),((5373219189:ℚ)/6147500000),((4685053209:ℚ)/4880000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((3367358493:ℚ)/10000000000),((-1310442237960846140987401346018016231730220937889429:ℚ)/18150376683349609375000000000000000000000000000000000),((-6981114321860312457019283:ℚ)/29573120000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7232559411:ℚ)/10000000000),((3677909833:ℚ)/5000000000),((54147915877:ℚ)/61950000000),((11801729499:ℚ)/12295000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((195140429:ℚ)/625000000),((-21449661713593858959761588265750169408330200694792807853:ℚ)/297189831093750000000000000000000000000000000000000000000),((-43524860416640236369012043:ℚ)/184832000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1458389667:ℚ)/2000000000),((373730697:ℚ)/500000000),((641925157:ℚ)/740000000),((399330697:ℚ)/413000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1428459571:ℚ)/5000000000),((-26803949295576501164334750493744912026781211719679:ℚ)/379897500000000000000000000000000000000000000000000),((-433106084999417614667083:ℚ)/1848320000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((463170347:ℚ)/625000000),((120503103:ℚ)/156250000),((1154064143:ℚ)/1350000000),((385509309:ℚ)/393125000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2236452431:ℚ)/10000000000),((-7691716498512881738861957714919075657621184704829:ℚ)/113906250000000000000000000000000000000000000000000),((-59673687:ℚ)/256000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((956034699:ℚ)/1250000000),((1922546199:ℚ)/2000000000),((7132242893:ℚ)/10000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-8892013001012653733849814277263487686088230831784639:ℚ)/234375000000000000000000000000000000000000000000000000),((-59673687:ℚ)/256000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((95486049:ℚ)/100000000),((13413355883:ℚ)/10000000000),((703602343:ℚ)/1104000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1505802169285874076061961933629:ℚ)/67278643200000000000000000000000),((-59673687:ℚ)/256000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC31
#check @N11Formalization.C450Source13GroupedC31.bound
#print axioms N11Formalization.C450Source13GroupedC31.valid0
#print axioms N11Formalization.C450Source13GroupedC31.valid1
#print axioms N11Formalization.C450Source13GroupedC31.valid2
#print axioms N11Formalization.C450Source13GroupedC31.valid3
#print axioms N11Formalization.C450Source13GroupedC31.valid4
#print axioms N11Formalization.C450Source13GroupedC31.valid5
#print axioms N11Formalization.C450Source13GroupedC31.valid6
#print axioms N11Formalization.C450Source13GroupedC31.valid7
#print axioms N11Formalization.C450Source13GroupedC31.valid8
#print axioms N11Formalization.C450Source13GroupedC31.valid9
#print axioms N11Formalization.C450Source13GroupedC31.valid10
#print axioms N11Formalization.C450Source13GroupedC31.valid11
#print axioms N11Formalization.C450Source13GroupedC31.valid12
#print axioms N11Formalization.C450Source13GroupedC31.valid13
#print axioms N11Formalization.C450Source13GroupedC31.valid14
#print axioms N11Formalization.C450Source13GroupedC31.valid15
#print axioms N11Formalization.C450Source13GroupedC31.bound
#print axioms N11Formalization.C450Source13GroupedC31.endpoint_checks
