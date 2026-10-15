import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6323395749:ℚ)/10000000000),((6602102949:ℚ)/10000000000),((-16286308847:ℚ)/49600000000),((-4787395749:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2940234193:ℚ)/5000000000),((15174231989191129631453888890568316740845250569190110611:ℚ)/338745370000000000000000000000000000000000000000000000000),((34421545422859275680901579:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((6561417221:ℚ)/10000000000),((1710038007:ℚ)/2500000000),((-4250114021:ℚ)/12875000000),((-5025417221:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5289361951:ℚ)/10000000000),((13970354865158274217885035484345650727258465902851845387:ℚ)/313683006240000000000000000000000000000000000000000000000),((2090890543585352407976771:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((13280081:ℚ)/19531250),((6959162123:ℚ)/10000000000),((-17357486369:ℚ)/53400000000),((-20560162:ℚ)/84921875),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4631310401:ℚ)/10000000000),((17806218247541725925623758737427325025806546365503:ℚ)/408799158693552017211914062500000000000000000000000),((32471252919782427289506091:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6918380863:ℚ)/10000000000),((350933189:ℚ)/500000000),((-876799567:ℚ)/2717500000),((-316610639:ℚ)/1290000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4267560533:ℚ)/10000000000),((10476238825170156340619833253837270834807567396814259:ℚ)/243067806562500000000000000000000000000000000000000000),((79949790419856554000059:ℚ)/1155200000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((6977867569:ℚ)/10000000000),((3539081627:ℚ)/5000000000),((-8857244881:ℚ)/27412500000),((-5441867569:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4074344149:ℚ)/10000000000),((19964334814003900718634800513529664789721655334317585617:ℚ)/463579303451250000000000000000000000000000000000000000000),((7934641267131691241406091:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7037352351:ℚ)/10000000000),((3568830301:ℚ)/5000000000),((-1278070129:ℚ)/3950000000),((-5501352351:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3872067423:ℚ)/10000000000),((2949254903667594086399682239813205414234328009479939529:ℚ)/68535538975703125000000000000000000000000000000000000000),((7874323453390756880367579:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((3548417629:ℚ)/5000000000),((7197155877:ℚ)/10000000000),((-18071467631:ℚ)/55775000000),((-2780417629:ℚ)/11250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((914806007:ℚ)/2500000000),((2000889189364464712752386457854234900529955919722320793:ℚ)/46531648635864257812500000000000000000000000000000000000),((31256102197254874770694091:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7156316337:ℚ)/10000000000),((7256649131:ℚ)/10000000000),((-18249947393:ℚ)/56250000000),((-5620316337:ℚ)/22690000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((53653833:ℚ)/156250000),((14117598663538900049815841943691836421359342765734377:ℚ)/328545874940625000000000000000000000000000000000000000),((31014990022316583558483819:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((1803948909:ℚ)/2500000000),((57157347:ℚ)/78125000),((-287944082:ℚ)/886328125),((-1419948909:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((399159197:ℚ)/1250000000),((22792889064860562156715652251026607490020054837370533089:ℚ)/530802054640000000000000000000000000000000000000000000000),((30052692468275250644001:ℚ)/451250000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7275273197:ℚ)/10000000000),((368781489:ℚ)/500000000),((-71564959:ℚ)/220000000),((-5739273197:ℚ)/23070000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((586753749:ℚ)/2000000000),((77181685707975065145178884167520631952762985517399:ℚ)/1798597916455078125000000000000000000000000000000000),((76332508041171096684659:ℚ)/1155200000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1466949813:ℚ)/2000000000),((743511727:ℚ)/1000000000),((-1878535181:ℚ)/5767500000),((-1159749813:ℚ)/4652000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2649768603:ℚ)/10000000000),((12450345280487708901623275800113772042305544445518013799:ℚ)/290319846586320000000000000000000000000000000000000000000),((302921282202812177822691:ℚ)/4620800000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7394223281:ℚ)/10000000000),((755408681:ℚ)/1000000000),((-1914226043:ℚ)/5815000000),((-5858223281:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1166168041:ℚ)/5000000000),((7681865328335596315684306203293085605361998073326285961:ℚ)/177831375980000000000000000000000000000000000000000000000),((300604437038201477207219:ℚ)/4620800000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((1878291729:ℚ)/2500000000),((7792005323:ℚ)/10000000000),((-19856015969:ℚ)/59100000000),((-1494291729:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((94568217:ℚ)/625000000),((7342816447144666394724938661387992492562560277858564151:ℚ)/167682213750000000000000000000000000000000000000000000000),((3890509672227591:ℚ)/60800000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((1937759013:ℚ)/2500000000),((1653553709:ℚ)/2000000000),((-4256661127:ℚ)/12200000000),((-517919671:ℚ)/2160000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((11490952020017522949587700778357801256669971891290113:ℚ)/256141440000000000000000000000000000000000000000000000),((252797:ℚ)/4000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((1645341849:ℚ)/2000000000),((10170095097:ℚ)/10000000000),((-26990285291:ℚ)/64800000000),((-1338141849:ℚ)/6400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1340914366771390154303903526571820868698367202004767001:ℚ)/26542080000000000000000000000000000000000000000000000000),((252797:ℚ)/4000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((2532190373:ℚ)/2500000000),((436650757:ℚ)/312500000),((-1199952271:ℚ)/2500000000),((-2148190373:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((72326827807929909245347071659137000657847421732749599:ℚ)/1261474560000000000000000000000000000000000000000000000),((252797:ℚ)/4000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC11
#check @N11Formalization.C450Source13GroupedC11.bound
#print axioms N11Formalization.C450Source13GroupedC11.valid0
#print axioms N11Formalization.C450Source13GroupedC11.valid1
#print axioms N11Formalization.C450Source13GroupedC11.valid2
#print axioms N11Formalization.C450Source13GroupedC11.valid3
#print axioms N11Formalization.C450Source13GroupedC11.valid4
#print axioms N11Formalization.C450Source13GroupedC11.valid5
#print axioms N11Formalization.C450Source13GroupedC11.valid6
#print axioms N11Formalization.C450Source13GroupedC11.valid7
#print axioms N11Formalization.C450Source13GroupedC11.valid8
#print axioms N11Formalization.C450Source13GroupedC11.valid9
#print axioms N11Formalization.C450Source13GroupedC11.valid10
#print axioms N11Formalization.C450Source13GroupedC11.valid11
#print axioms N11Formalization.C450Source13GroupedC11.valid12
#print axioms N11Formalization.C450Source13GroupedC11.valid13
#print axioms N11Formalization.C450Source13GroupedC11.valid14
#print axioms N11Formalization.C450Source13GroupedC11.valid15
#print axioms N11Formalization.C450Source13GroupedC11.bound
#print axioms N11Formalization.C450Source13GroupedC11.endpoint_checks
