import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((583256879:ℚ)/1000000000),((6385294781:ℚ)/10000000000),((951256879:ℚ)/2670000000),((9457294781:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((217485217:ℚ)/312500000),((7228867334036434064925482829380758148843:ℚ)/139183429976064000000000000000000000000000),((-219152867183282646249694401:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3156207229:ℚ)/5000000000),((414053981:ℚ)/625000000),((4996207229:ℚ)/13825000000),((606053981:ℚ)/1335000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2953232217:ℚ)/5000000000),((27073312291766980827626773573550456709688193256417426247:ℚ)/649644905453906250000000000000000000000000000000000000000),((-893996124872451103670801:ℚ)/2310400000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((3276042039:ℚ)/5000000000),((1348919017:ℚ)/2000000000),((5116042039:ℚ)/14062500000),((1963319017:ℚ)/4424000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5313647789:ℚ)/10000000000),((233516995736779782048071064425330642514189047644110491:ℚ)/6261989731200000000000000000000000000000000000000000000),((-9347330365235982998019849:ℚ)/23658496000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((6671863203:ℚ)/10000000000),((1716073371:ℚ)/2500000000),((941078473:ℚ)/2600000000),((828024457:ℚ)/1875000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1248465139:ℚ)/2500000000),((86201502657815398527116936883071279836773089269516951:ℚ)/2320861816406250000000000000000000000000000000000000000),((-44162338684350719227681843:ℚ)/110899200000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3395803857:ℚ)/5000000000),((1396792107:ℚ)/2000000000),((5235803857:ℚ)/14537500000),((2011192107:ℚ)/4576000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2327106187:ℚ)/5000000000),((7502120764628955428058005809021149076006189771529139424527:ℚ)/202505816974489600000000000000000000000000000000000000000000),((-28483413535934083533398227:ℚ)/70975488000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6911319333:ℚ)/10000000000),((1775899443:ℚ)/2500000000),((10591319333:ℚ)/29550000000),((2543899443:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4289952959:ℚ)/10000000000),((441189233910061333495715469912119138934965725734005714007:ℚ)/11923441781899023437500000000000000000000000000000000000000),((-44844604024030460925886627:ℚ)/110899200000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3515499837:ℚ)/5000000000),((902900829:ℚ)/1250000000),((5355499837:ℚ)/15012500000),((428966943:ℚ)/985000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((121692003:ℚ)/312500000),((318818791290940728837945101234483887827872461860549108747:ℚ)/8615385672322656250000000000000000000000000000000000000000),((-11295039334832283321864643:ℚ)/27724800000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((3575325121:ℚ)/5000000000),((7342788459:ℚ)/10000000000),((5415325121:ℚ)/15250000000),((10414788459:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((691184257:ℚ)/2000000000),((11943070823101886517746204355418484818914802338674595158359:ℚ)/322298805966050000000000000000000000000000000000000000000000),((-728192009973543434126439763:ℚ)/1774387200000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((145405449:ℚ)/200000000),((3790937989:ℚ)/5000000000),((219005449:ℚ)/629000000),((5326937989:ℚ)/12200000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1478218481:ℚ)/5000000000),((45352770743223516321489599816828506007061851037391541425009:ℚ)/1122537372762500000000000000000000000000000000000000000000000),((-60816599886935273341546961:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7509436997:ℚ)/10000000000),((7820869521:ℚ)/10000000000),((11189436997:ℚ)/32400000000),((10892869521:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((386327679:ℚ)/2500000000),((26505431223353040552792547395993773238680380776761796615269:ℚ)/653103431211600000000000000000000000000000000000000000000000),((-409489101197455307:ℚ)/972800000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((1937125741:ℚ)/2500000000),((9730245983:ℚ)/10000000000),((2857125741:ℚ)/10000000000),((12802245983:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((501264555563015111457533404953673577860307888272152523:ℚ)/6802444800000000000000000000000000000000000000000000000),((-434901739:ℚ)/1024000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9658333191:ℚ)/10000000000),((1692652499:ℚ)/1250000000),((13338333191:ℚ)/55200000000),((2076652499:ℚ)/4000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((11037499191862991308831069:ℚ)/95220000000000000000000000),((-434901739:ℚ)/1024000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC21
#check @N11Formalization.C450Source25GroupedC21.bound
#print axioms N11Formalization.C450Source25GroupedC21.valid0
#print axioms N11Formalization.C450Source25GroupedC21.valid1
#print axioms N11Formalization.C450Source25GroupedC21.valid2
#print axioms N11Formalization.C450Source25GroupedC21.valid3
#print axioms N11Formalization.C450Source25GroupedC21.valid4
#print axioms N11Formalization.C450Source25GroupedC21.valid5
#print axioms N11Formalization.C450Source25GroupedC21.valid6
#print axioms N11Formalization.C450Source25GroupedC21.valid7
#print axioms N11Formalization.C450Source25GroupedC21.valid8
#print axioms N11Formalization.C450Source25GroupedC21.valid9
#print axioms N11Formalization.C450Source25GroupedC21.valid10
#print axioms N11Formalization.C450Source25GroupedC21.valid11
#print axioms N11Formalization.C450Source25GroupedC21.bound
#print axioms N11Formalization.C450Source25GroupedC21.endpoint_checks
