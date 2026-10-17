import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/16),((3:ℚ)/8),((358411351:ℚ)/625000000),((6054529333:ℚ)/10000000000),((558411351:ℚ)/1287500000),((26483587999:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3579139381:ℚ)/5000000000),((-14212095817178864364149:ℚ)/828828125000000000000000),((-753880189110249578653481651:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((5974896403:ℚ)/10000000000),((1258912597:ℚ)/2000000000),((3058298801:ℚ)/7120000000),((52822697:ℚ)/100000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6662083633:ℚ)/10000000000),((-287074560608365832730233786030069:ℚ)/15842000000000000000000000000000000),((-30544595776448790876169331:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((388437973:ℚ)/625000000),((653441993:ℚ)/1000000000),((588437973:ℚ)/1382500000),((2792325979:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6132807877:ℚ)/10000000000),((-25655594499620500391034265334451:ℚ)/1365218750000000000000000000000000),((-7730549420265234356932091:ℚ)/18483200000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((3227468269:ℚ)/5000000000),((6654287843:ℚ)/10000000000),((4827468269:ℚ)/11250000000),((28282863529:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1390186223:ℚ)/2500000000),((-14967598384446218458375093878098281:ℚ)/632812500000000000000000000000000000),((-786194360629049293477267491:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((3287419293:ℚ)/5000000000),((6774118113:ℚ)/10000000000),((4887419293:ℚ)/11440000000),((28642354339:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1313565031:ℚ)/2500000000),((-15480200748205397477610317620274369:ℚ)/654368000000000000000000000000000000),((-790728374168116161682122571:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((3347350913:ℚ)/5000000000),((344695631:ℚ)/500000000),((4947350913:ℚ)/11630000000),((1450086893:ℚ)/2860000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4930743571:ℚ)/10000000000),((-7983400137205355526305389697754333:ℚ)/338142250000000000000000000000000000),((-1987973991405257413728299:ℚ)/4620800000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1703632049:ℚ)/2500000000),((7013673117:ℚ)/10000000000),((2503632049:ℚ)/5910000000),((29361019351:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4586557913:ℚ)/10000000000),((-228136563281328228769711733030749:ℚ)/9702250000000000000000000000000000),((-799578168393622368077698851:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((1386863901:ℚ)/2000000000),((1426680249:ℚ)/2000000000),((2026863901:ℚ)/4804000000),((5944040747:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2108304143:ℚ)/5000000000),((-2696915163990257497050205586271303:ℚ)/115392080000000000000000000000000000),((-32155768834057462510536859:ℚ)/73932800000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((3527038723:ℚ)/5000000000),((7253098541:ℚ)/10000000000),((5127038723:ℚ)/12200000000),((30079295623:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3813364629:ℚ)/10000000000),((-17254870839588264875402147984743967:ℚ)/744200000000000000000000000000000000),((-808137876702486695200094979:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((1793450901:ℚ)/2500000000),((7731606929:ℚ)/10000000000),((2593450901:ℚ)/6480000000),((31514820787:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3364835447:ℚ)/10000000000),((-1227831866184009350031430505141747:ℚ)/104976000000000000000000000000000000),((-1322150703626543:ℚ)/3040000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((1913104697:ℚ)/2500000000),((385691223:ℚ)/400000000),((2713104697:ℚ)/8000000000),((1489873669:ℚ)/2592000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1748364597412896017157235971441489:ℚ)/80000000000000000000000000000000000),((-57768377:ℚ)/128000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((597713531:ℚ)/625000000),((13454767569:ℚ)/10000000000),((34683197:ℚ)/120000000),((48684302707:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((499546609208092406659:ℚ)/7200000000000000000000),((-57768377:ℚ)/128000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC22
#check @N11Formalization.C450Source27GroupedC22.bound
#print axioms N11Formalization.C450Source27GroupedC22.valid0
#print axioms N11Formalization.C450Source27GroupedC22.valid1
#print axioms N11Formalization.C450Source27GroupedC22.valid2
#print axioms N11Formalization.C450Source27GroupedC22.valid3
#print axioms N11Formalization.C450Source27GroupedC22.valid4
#print axioms N11Formalization.C450Source27GroupedC22.valid5
#print axioms N11Formalization.C450Source27GroupedC22.valid6
#print axioms N11Formalization.C450Source27GroupedC22.valid7
#print axioms N11Formalization.C450Source27GroupedC22.valid8
#print axioms N11Formalization.C450Source27GroupedC22.valid9
#print axioms N11Formalization.C450Source27GroupedC22.valid10
#print axioms N11Formalization.C450Source27GroupedC22.valid11
#print axioms N11Formalization.C450Source27GroupedC22.bound
#print axioms N11Formalization.C450Source27GroupedC22.endpoint_checks
