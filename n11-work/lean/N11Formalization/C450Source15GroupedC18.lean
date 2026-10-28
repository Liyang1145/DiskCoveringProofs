import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6105054653:ℚ)/10000000000),((6622293857:ℚ)/10000000000),((4808351551:ℚ)/35600000000),((11102293857:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((199370739:ℚ)/312500000),((10062154637837964334112788090094018263339:ℚ)/241637899264000000000000000000000000000000),((-232040435595199084219002411:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((658183621:ℚ)/1000000000),((6860490101:ℚ)/10000000000),((1490183621:ℚ)/11060000000),((3780163367:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1308968557:ℚ)/2500000000),((426590791804326410731166859065231946159310261814358589500223:ℚ)/10779293246050000000000000000000000000000000000000000000000000),((-246375924991634139092401939:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((3410067351:ℚ)/5000000000),((6979570511:ℚ)/10000000000),((7570067351:ℚ)/56250000000),((11459570511:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4569867711:ℚ)/10000000000),((473916845388161804079663780329918396686059317028938724953:ℚ)/12230448693750000000000000000000000000000000000000000000000),((-253539355470438180050999819:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((3469631811:ℚ)/5000000000),((7098639901:ℚ)/10000000000),((7629631811:ℚ)/57200000000),((11578639901:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4200685093:ℚ)/10000000000),((97364254855435621258103110850389767494234034710694894293341:ℚ)/2527418518066406250000000000000000000000000000000000000000000),((-257089892336163195198446339:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((3529189949:ℚ)/5000000000),((1431634127:ℚ)/2000000000),((7689189949:ℚ)/57675000000),((179048779:ℚ)/880000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1899062093:ℚ)/5000000000),((72123169125811694186274369741453119554597185680966965073:ℚ)/1889043578400000000000000000000000000000000000000000000000),((-10426788932215402319601931:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((711793349:ℚ)/1000000000),((3608849407:ℚ)/5000000000),((1543793349:ℚ)/11630000000),((1949616469:ℚ)/9612500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3580836201:ℚ)/10000000000),((11438932084224332765061228424995495909576559793197443628429:ℚ)/300336763612559082031250000000000000000000000000000000000000),((-65611007551905186131615211:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/16),((1:ℚ)/8),((897185519:ℚ)/1250000000),((3638612251:ℚ)/5000000000),((1937185519:ℚ)/14656250000),((5878612251:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3350136879:ℚ)/10000000000),((320995323599803554551877313870485329207002401698038330818211:ℚ)/8447435445992846679687500000000000000000000000000000000000000),((-66054498862739098360857139:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((3618515977:ℚ)/5000000000),((7336747759:ℚ)/10000000000),((2592838659:ℚ)/19700000000),((11816747759:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((193939471:ℚ)/625000000),((463258298870189313856823021478828191219523116623433251363111:ℚ)/12218026014956665039062500000000000000000000000000000000000000),((-265991621157337460826653259:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7296576967:ℚ)/10000000000),((7455787211:ℚ)/10000000000),((15616576967:ℚ)/120100000000),((3978595737:ℚ)/19700000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1417614261:ℚ)/5000000000),((2616953782455103405095174545066435715552686520721600442105017:ℚ)/68923085378581250000000000000000000000000000000000000000000000),((-267733209319847316144278419:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7415658891:ℚ)/10000000000),((1514963523:ℚ)/2000000000),((15735658891:ℚ)/122000000000),((2410963523:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2206993543:ℚ)/10000000000),((1523741820933461218714899590744784644208471634479483095763:ℚ)/40287350745756250000000000000000000000000000000000000000000),((-10851131045395543964398531:ℚ)/73932800000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7534730433:ℚ)/10000000000),((4025428373:ℚ)/5000000000),((15854730433:ℚ)/129600000000),((6265428373:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((163939983:ℚ)/1250000000),((11172155983167706830178469900346900628583588734338079559893:ℚ)/290863738476562500000000000000000000000000000000000000000000),((-7233512718630367:ℚ)/48640000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((320436879:ℚ)/400000000),((1990804747:ℚ)/2000000000),((653236879:ℚ)/6400000000),((320756083:ℚ)/1440000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((15634581842496707994505099694768367947478420931369:ℚ)/388800000000000000000000000000000000000000000000000),((-19172557:ℚ)/128000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((9914553067:ℚ)/10000000000),((6878868859:ℚ)/5000000000),((18234553067:ℚ)/220800000000),((9118868859:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3552651467470392084764280434085106933897:ℚ)/76176000000000000000000000000000000000000),((-19172557:ℚ)/128000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC18
#check @N11Formalization.C450Source15GroupedC18.bound
#print axioms N11Formalization.C450Source15GroupedC18.valid0
#print axioms N11Formalization.C450Source15GroupedC18.valid1
#print axioms N11Formalization.C450Source15GroupedC18.valid2
#print axioms N11Formalization.C450Source15GroupedC18.valid3
#print axioms N11Formalization.C450Source15GroupedC18.valid4
#print axioms N11Formalization.C450Source15GroupedC18.valid5
#print axioms N11Formalization.C450Source15GroupedC18.valid6
#print axioms N11Formalization.C450Source15GroupedC18.valid7
#print axioms N11Formalization.C450Source15GroupedC18.valid8
#print axioms N11Formalization.C450Source15GroupedC18.valid9
#print axioms N11Formalization.C450Source15GroupedC18.valid10
#print axioms N11Formalization.C450Source15GroupedC18.valid11
#print axioms N11Formalization.C450Source15GroupedC18.valid12
#print axioms N11Formalization.C450Source15GroupedC18.bound
#print axioms N11Formalization.C450Source15GroupedC18.endpoint_checks
