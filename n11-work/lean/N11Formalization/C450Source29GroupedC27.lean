import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/8),((11:ℚ)/16),((5376421721:ℚ)/10000000000),((1426763853:ℚ)/2500000000),((7104421721:ℚ)/10300000000),((20174402383:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3924747871:ℚ)/5000000000),((-906486754414587046455987607504636014062046912927546824566009:ℚ)/3034106102400000000000000000000000000000000000000000000000000),((-29765285156572536352960739:ℚ)/69312000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((2807957337:ℚ)/5000000000),((23228689:ℚ)/39062500),((1223985779:ℚ)/1780000000),((325515579:ℚ)/402343750),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3696531451:ℚ)/5000000000),((-3842029102868811300534551490690423474231521393317976559:ℚ)/12897686015069484710693359375000000000000000000000000000),((-19117337949980504435551:ℚ)/45125000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((5855264143:ℚ)/10000000000),((6185895079:ℚ)/10000000000),((1083323449:ℚ)/1580000000),((28654948623:ℚ)/35600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6912817623:ℚ)/10000000000),((-8168173174940813790536760561365221390319767923895984122403:ℚ)/27498197056250000000000000000000000000000000000000000000000),((-154374568892547760751338537:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((3047242569:ℚ)/5000000000),((6305523017:ℚ)/10000000000),((1303747523:ℚ)/1875000000),((87280753187:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3201588913:ℚ)/5000000000),((-90514696106182447884743614704895573804200304411074426727:ℚ)/297267850195312500000000000000000000000000000000000000000),((-153332027223145839384401673:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((24273639:ℚ)/39062500),((160628037:ℚ)/250000000),((31023639:ℚ)/44687500),((2214908407:ℚ)/2812500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((76687413:ℚ)/125000000),((-864142887544165531368120322518511189153249792276381483147:ℚ)/2843345832824707031250000000000000000000000000000000000000),((-285290383573233807371699:ℚ)/693120000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6333590639:ℚ)/10000000000),((1636172983:ℚ)/2500000000),((8061590639:ℚ)/11630000000),((22477902813:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5856242931:ℚ)/10000000000),((-5453963897788692006809901916201954677230152170726655899943067:ℚ)/17978144262650000000000000000000000000000000000000000000000000),((-9434612715635026346353673:ℚ)/23104000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6453103663:ℚ)/10000000000),((6664235743:ℚ)/10000000000),((8181103663:ℚ)/11820000000),((91226593173:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((556531203:ℚ)/1000000000),((-86659846690628340806656210807963967247576804201713831200110059:ℚ)/286162602765576562500000000000000000000000000000000000000000000),((-149728826667645345404255993:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6572591927:ℚ)/10000000000),((423984637:ℚ)/625000000),((8300591927:ℚ)/12010000000),((1927943669:ℚ)/2462500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((21040603:ℚ)/40000000),((-30522782586566617174045376819540111904105335654588368231787:ℚ)/100961550847531127929687500000000000000000000000000000000000),((-579999779502776854486033:ℚ)/1444000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((3346028311:ℚ)/5000000000),((6903248481:ℚ)/10000000000),((4210028311:ℚ)/6100000000),((93855733291:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2469045869:ℚ)/5000000000),((-36479249173760287139865331527676935011097639402051112956352453:ℚ)/120862052237268750000000000000000000000000000000000000000000000),((-441621469661930223046785131:ℚ)/1108992000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((340574943:ℚ)/500000000),((7142169007:ℚ)/10000000000),((426974943:ℚ)/629000000),((96483859077:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4595552611:ℚ)/10000000000),((-330148285578975498751746922833082407448061025248036098043275417:ℚ)/1122537372762500000000000000000000000000000000000000000000000000),((-144479370169650346065883993:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((1762580021:ℚ)/2500000000),((3690502763:ℚ)/5000000000),((2194580021:ℚ)/3240000000),((49555530393:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((956656747:ℚ)/2500000000),((-80943683147284800887833318566149986087084301298533240312521:ℚ)/275803813856250000000000000000000000000000000000000000000000),((-35441635282046080097062833:ℚ)/92416000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((3644531609:ℚ)/5000000000),((9289397877:ℚ)/10000000000),((4508531609:ℚ)/8000000000),((120103376647:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2870358657:ℚ)/10000000000),((-536360800033972062017904162495609348755946599161431717169:ℚ)/2550916800000000000000000000000000000000000000000000000000),((-11448402417921409:ℚ)/30400000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((4598435059:ℚ)/5000000000),((13099223211:ℚ)/10000000000),((5462435059:ℚ)/11040000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-9257032805615360554470701:ℚ)/60940800000000000000000000),((-48303431:ℚ)/128000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC27
#check @N11Formalization.C450Source29GroupedC27.bound
#print axioms N11Formalization.C450Source29GroupedC27.valid0
#print axioms N11Formalization.C450Source29GroupedC27.valid1
#print axioms N11Formalization.C450Source29GroupedC27.valid2
#print axioms N11Formalization.C450Source29GroupedC27.valid3
#print axioms N11Formalization.C450Source29GroupedC27.valid4
#print axioms N11Formalization.C450Source29GroupedC27.valid5
#print axioms N11Formalization.C450Source29GroupedC27.valid6
#print axioms N11Formalization.C450Source29GroupedC27.valid7
#print axioms N11Formalization.C450Source29GroupedC27.valid8
#print axioms N11Formalization.C450Source29GroupedC27.valid9
#print axioms N11Formalization.C450Source29GroupedC27.valid10
#print axioms N11Formalization.C450Source29GroupedC27.valid11
#print axioms N11Formalization.C450Source29GroupedC27.valid12
#print axioms N11Formalization.C450Source29GroupedC27.bound
#print axioms N11Formalization.C450Source29GroupedC27.endpoint_checks
