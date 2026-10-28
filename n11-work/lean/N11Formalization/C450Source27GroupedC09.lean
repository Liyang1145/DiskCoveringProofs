import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6571944247:ℚ)/10000000000),((846778837:ℚ)/1250000000),((-596778837:ℚ)/1550000000),((-29363609729:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((328865489:ℚ)/625000000),((1608963677797786975473765724470269459145941192015783136651:ℚ)/7415345893750000000000000000000000000000000000000000000000),((1924261001329906071994371143:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((3345969523:ℚ)/5000000000),((6894182793:ℚ)/10000000000),((-4894182793:ℚ)/12637500000),((-15101786661:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4938418121:ℚ)/10000000000),((62473489031975752534103038528143907168494602739716625239379:ℚ)/287694530468750000000000000000000000000000000000000000000000),((460746707868055357565867183:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6811887223:ℚ)/10000000000),((3477071059:ℚ)/5000000000),((-2477071059:ℚ)/6437500000),((-2822110051:ℚ)/9450000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2297200199:ℚ)/5000000000),((9700922055964890193670543689782327065528691908701443257:ℚ)/45272181445312500000000000000000000000000000000000000000),((1761133295423052923886800583:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6871844643:ℚ)/10000000000),((3507045353:ℚ)/5000000000),((-2507045353:ℚ)/6496875000),((-31462912501:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2206583033:ℚ)/5000000000),((267989654627250248440618853336997716539081977603199894994839:ℚ)/1249912827745312500000000000000000000000000000000000000000000),((5159966782581534349146161069:ℚ)/44359680000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6931791361:ℚ)/10000000000),((7074028851:ℚ)/10000000000),((-5074028851:ℚ)/13112500000),((-31882539527:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4224728709:ℚ)/10000000000),((1668093513825688682109080531744094975942854390799391931825969:ℚ)/7775495826591406250000000000000000000000000000000000000000000),((1678699323053178204181423767:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((6991727671:ℚ)/10000000000),((1783489209:ℚ)/2500000000),((-1283489209:ℚ)/3307812500),((-362944873:ℚ)/1200000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1007018153:ℚ)/2500000000),((136328145494873571459272444828735061674057351716984507:ℚ)/635100000000000000000000000000000000000000000000000000),((1637264360091073344666497607:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((1410330771:ℚ)/2000000000),((7193874937:ℚ)/10000000000),((-5193874937:ℚ)/13350000000),((-6544315397:ℚ)/21550000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3821924187:ℚ)/10000000000),((4670499941760041622490349656534823475670293249507313099:ℚ)/21745624386596679687500000000000000000000000000000000000),((191482070647916266055939021:ℚ)/1774387200000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7111570187:ℚ)/10000000000),((906722927:ℚ)/1250000000),((-656722927:ℚ)/1683593750),((-33140991309:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3604649879:ℚ)/10000000000),((743502280899485761456637978486374746398870713994324840247533:ℚ)/3459759573706250000000000000000000000000000000000000000000000),((1553957895101254232032692063:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7171476929:ℚ)/10000000000),((7313682529:ℚ)/10000000000),((-5313682529:ℚ)/13587500000),((-658045853:ℚ)/2150000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((421761929:ℚ)/1250000000),((3629467639338058468404535034739602476105321218220584573:ℚ)/16879708789062500000000000000000000000000000000000000000),((1512086170922412627199421207:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((1446274867:ℚ)/2000000000),((184339313:ℚ)/250000000),((-44779771:ℚ)/114218750),((-6795924069:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3127319147:ℚ)/10000000000),((166222168612140664646474363946733355769357408742652842417:ℚ)/772632172418750000000000000000000000000000000000000000000),((58802745767987039235667503:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((145825253:ℚ)/200000000),((7493326079:ℚ)/10000000000),((-5493326079:ℚ)/13825000000),((-687976771:ℚ)/2250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2860118779:ℚ)/10000000000),((11175447561440830905645119687574046232503997194326047:ℚ)/51261520385742187500000000000000000000000000000000000),((571162085342434084230143:ℚ)/5914624000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((463188309:ℚ)/625000000),((7613045893:ℚ)/10000000000),((-5613045893:ℚ)/14062500000),((-2202318163:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1117373389:ℚ)/5000000000),((1495256054575246832046485983791924822702597826794484847:ℚ)/6853610156250000000000000000000000000000000000000000000),((15739924816805193231959261:ℚ)/173280000000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((1882682401:ℚ)/2500000000),((809161971:ℚ)/1000000000),((-55378361:ℚ)/130000000),((-9018776807:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((67558883:ℚ)/500000000),((538417382029798667994379184570906210270347129558752671373:ℚ)/2305275781250000000000000000000000000000000000000000000000),((78611908840509083893488727:ℚ)/924160000000000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((800929181:ℚ)/1000000000),((4284885093:ℚ)/5000000000),((-3284885093:ℚ)/7625000000),((-1314168089:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((265104907321189446543772630047551011478761376181369209:ℚ)/1138406400000000000000000000000000000000000000000000000),((83665349:ℚ)/1024000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((4243716031:ℚ)/5000000000),((10479357411:ℚ)/10000000000),((-8479357411:ℚ)/16200000000),((-21386012217:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((24125433210943331162290806604193328865430795869873083355837:ℚ)/86400000000000000000000000000000000000000000000000000000000),((83665349:ℚ)/1024000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((41587953:ℚ)/40000000),((3572644333:ℚ)/2500000000),((-3072644333:ℚ)/5000000000),((-224555671:ℚ)/883200000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((117149422339621926809402888321463712365964871791339:ℚ)/358819430400000000000000000000000000000000000000000),((83665349:ℚ)/1024000000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC09
#check @N11Formalization.C450Source27GroupedC09.bound
#print axioms N11Formalization.C450Source27GroupedC09.valid0
#print axioms N11Formalization.C450Source27GroupedC09.valid1
#print axioms N11Formalization.C450Source27GroupedC09.valid2
#print axioms N11Formalization.C450Source27GroupedC09.valid3
#print axioms N11Formalization.C450Source27GroupedC09.valid4
#print axioms N11Formalization.C450Source27GroupedC09.valid5
#print axioms N11Formalization.C450Source27GroupedC09.valid6
#print axioms N11Formalization.C450Source27GroupedC09.valid7
#print axioms N11Formalization.C450Source27GroupedC09.valid8
#print axioms N11Formalization.C450Source27GroupedC09.valid9
#print axioms N11Formalization.C450Source27GroupedC09.valid10
#print axioms N11Formalization.C450Source27GroupedC09.valid11
#print axioms N11Formalization.C450Source27GroupedC09.valid12
#print axioms N11Formalization.C450Source27GroupedC09.valid13
#print axioms N11Formalization.C450Source27GroupedC09.valid14
#print axioms N11Formalization.C450Source27GroupedC09.valid15
#print axioms N11Formalization.C450Source27GroupedC09.bound
#print axioms N11Formalization.C450Source27GroupedC09.endpoint_checks
