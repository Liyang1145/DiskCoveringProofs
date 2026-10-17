import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/2),((9:ℚ)/16),((1381965283:ℚ)/2500000000),((5854182793:ℚ)/10000000000),((1901965283:ℚ)/3218750000),((69967645137:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7563435759:ℚ)/10000000000),((-1471452896060442602176924044703059:ℚ)/8336845397949218750000000000000000),((-6127503957943294837911639:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((450607:ℚ)/781250),((1523489209:ℚ)/2500000000),((817476:ℚ)/1390625),((18031402881:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7091478627:ℚ)/10000000000),((-11565346057219261448885480471064450395559:ℚ)/65655354410409927368164062500000000000000),((-382343557376537466811191:ℚ)/902500000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6007504249:ℚ)/10000000000),((776722927:ℚ)/1250000000),((8087504249:ℚ)/13587500000),((3050168781:ℚ)/4450000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((263693967:ℚ)/400000000),((-8644758107824534236273135835908976806082678840314828977:ℚ)/47034869494628906250000000000000000000000000000000000000),((-384085863430445105058801:ℚ)/902500000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6127312193:ℚ)/10000000000),((158339313:ℚ)/250000000),((8207312193:ℚ)/13825000000),((1857053817:ℚ)/2717500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3165263293:ℚ)/5000000000),((-189241452686841445238965569820955965008524330140735563:ℚ)/1032180035400390625000000000000000000000000000000000000),((-15346004646547123164961:ℚ)/36100000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((3123541659:ℚ)/5000000000),((6453326079:ℚ)/10000000000),((4163541659:ℚ)/7031250000),((75359934711:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1211818373:ℚ)/2000000000),((-132439116791018972070590349468377144292379401835100347:ℚ)/724196434020996093750000000000000000000000000000000000),((-322665726110341313967229:ℚ)/760000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((6366819521:ℚ)/10000000000),((6573045893:ℚ)/10000000000),((8446819521:ℚ)/14300000000),((8493045893:ℚ)/12500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((46213287:ℚ)/80000000),((-303058125039165628113328851384776638836947271496867809:ℚ)/1661481250000000000000000000000000000000000000000000000),((-6122115217586264735734239:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6486522569:ℚ)/10000000000),((6692733643:ℚ)/10000000000),((8566522569:ℚ)/14537500000),((77514602787:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1370376067:ℚ)/2500000000),((-873297402499855494156363765059643266156409221717269179:ℚ)/4800530233764648437500000000000000000000000000000000000),((-6112801672643162611258239:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3303097057:ℚ)/5000000000),((3406195449:ℚ)/5000000000),((1447699019:ℚ)/2462500000),((39295759041:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5171412909:ℚ)/10000000000),((-12698653219377885504139879064926725876837397478249003:ℚ)/69995480346679687500000000000000000000000000000000000),((-1525677168922157555345311:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3362917849:ℚ)/5000000000),((6932019129:ℚ)/10000000000),((4402917849:ℚ)/7506250000),((26556057387:ℚ)/39400000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4843487467:ℚ)/10000000000),((-478215936082960555854199045703750875227095432566602579:ℚ)/2643316041564941406250000000000000000000000000000000000),((-6091836705819618924705751:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((1711362191:ℚ)/2500000000),((705161971:ℚ)/1000000000),((2231362191:ℚ)/3812500000),((8074457739:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4493792297:ℚ)/10000000000),((-62480534032275372578410142945598302647087436814200421:ℚ)/346345520019531250000000000000000000000000000000000000),((-60801862127734083243951:ℚ)/144400000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3482517331:ℚ)/5000000000),((1458148601:ℚ)/2000000000),((4522517331:ℚ)/7862500000),((16579337409:ℚ)/24400000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2058374211:ℚ)/5000000000),((-131477812521078622193248611995568881439112991339219361:ℚ)/759454922485351562500000000000000000000000000000000000),((-240823094393721298741911:ℚ)/577600000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7204129949:ℚ)/10000000000),((3764885093:ℚ)/5000000000),((3094709983:ℚ)/5400000000),((42523965837:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((12663331:ℚ)/39062500),((-6280532569987485191529149667488646090613569469107359:ℚ)/36450000000000000000000000000000000000000000000000000),((-78840089598060339723681:ℚ)/190000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((1860782699:ℚ)/2500000000),((9439357411:ℚ)/10000000000),((2380782699:ℚ)/5000000000),((11359357411:ℚ)/14400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2035292831:ℚ)/10000000000),((-610546742185002707731889293577599:ℚ)/5859375000000000000000000000000000),((-12696346589046789:ℚ)/30400000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((4676276511:ℚ)/5000000000),((3312644333:ℚ)/2500000000),((5716276511:ℚ)/13800000000),((34133798997:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-33016584360051613944887:ℚ)/661250000000000000000000),((-6731679:ℚ)/16000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC25
#check @N11Formalization.C450Source28GroupedC25.bound
#print axioms N11Formalization.C450Source28GroupedC25.valid0
#print axioms N11Formalization.C450Source28GroupedC25.valid1
#print axioms N11Formalization.C450Source28GroupedC25.valid2
#print axioms N11Formalization.C450Source28GroupedC25.valid3
#print axioms N11Formalization.C450Source28GroupedC25.valid4
#print axioms N11Formalization.C450Source28GroupedC25.valid5
#print axioms N11Formalization.C450Source28GroupedC25.valid6
#print axioms N11Formalization.C450Source28GroupedC25.valid7
#print axioms N11Formalization.C450Source28GroupedC25.valid8
#print axioms N11Formalization.C450Source28GroupedC25.valid9
#print axioms N11Formalization.C450Source28GroupedC25.valid10
#print axioms N11Formalization.C450Source28GroupedC25.valid11
#print axioms N11Formalization.C450Source28GroupedC25.valid12
#print axioms N11Formalization.C450Source28GroupedC25.valid13
#print axioms N11Formalization.C450Source28GroupedC25.bound
#print axioms N11Formalization.C450Source28GroupedC25.endpoint_checks
