import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5831865629:ℚ)/10000000000),((1272969629:ℚ)/2000000000),((23730173973:ℚ)/35600000000),((4202908887:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1392193989:ℚ)/2000000000),((-62337338911639671172447597874489999:ℚ)/2255900800000000000000000000000000000),((-13341715054454924905896903:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((157686129:ℚ)/250000000),((3301305667:ℚ)/5000000000),((1910547419:ℚ)/2765000000),((3621305667:ℚ)/4450000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((739774399:ℚ)/1250000000),((-2604787732374434574021147863602890621818047385721697:ℚ)/79271426718750000000000000000000000000000000000000000),((-8327826741964556196403:ℚ)/36100000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6545205009:ℚ)/10000000000),((6840357011:ℚ)/10000000000),((7185205009:ℚ)/10400000000),((22441071033:ℚ)/27650000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1332870953:ℚ)/2500000000),((-46527875026909422603394904217895076641405025141666161:ℚ)/1406080000000000000000000000000000000000000000000000000),((-13305204423364926544333423:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((423934223:ℚ)/625000000),((6959223821:ℚ)/10000000000),((5103276453:ℚ)/7268750000),((22797671463:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1169884589:ℚ)/2500000000),((-4246698331432173653877912661776644550264769952951877:ℚ)/120013255844116210937500000000000000000000000000000000),((-103881488257171187583989:ℚ)/451250000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((1380362579:ℚ)/2000000000),((1754663951:ℚ)/2500000000),((16591988369:ℚ)/23450000000),((5743991853:ℚ)/7268750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((53999079:ℚ)/125000000),((-63031027119316266390318614244203319305739481372869709:ℚ)/1727037539062500000000000000000000000000000000000000000),((-531707071659259160961703:ℚ)/2310400000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1392248831:ℚ)/2000000000),((7078086869:ℚ)/10000000000),((16722737141:ℚ)/23640000000),((23154260607:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2064597473:ℚ)/5000000000),((-5581886733323845382484925155936982774245333067921687:ℚ)/152907460000000000000000000000000000000000000000000000),((-531515784834868744517263:ℚ)/2310400000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((7020674509:ℚ)/10000000000),((89218963:ℚ)/125000000),((84267419599:ℚ)/119150000000),((97218963:ℚ)/123125000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3929774713:ℚ)/10000000000),((-231607279092902399528185511964645199406745230601348645677:ℚ)/6343273072031250000000000000000000000000000000000000000000),((-13283118053170639432216423:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((354005199:ℚ)/500000000),((224904573:ℚ)/312500000),((4246057189:ℚ)/6005000000),((734713719:ℚ)/930859375),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1860132351:ℚ)/5000000000),((-617790637696876484916199628790785664750729968293709:ℚ)/16917222666015625000000000000000000000000000000000000),((-33195867716613004177583:ℚ)/144400000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((7139532587:ℚ)/10000000000),((7256374779:ℚ)/10000000000),((28524952819:ℚ)/40350000000),((23689124337:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3498848759:ℚ)/10000000000),((-999751878905748855931458045271366091587637419848833513:ℚ)/27372809531250000000000000000000000000000000000000000000),((-698609564171170915081133:ℚ)/3040000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((224967511:ℚ)/312500000),((7315802389:ℚ)/10000000000),((2694642621:ℚ)/3812500000),((7955802389:ℚ)/10087500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((815774951:ℚ)/2500000000),((-2530234204661113350705990669065192141200459419170981:ℚ)/69269104003906250000000000000000000000000000000000000),((-103662671477907477857319:ℚ)/451250000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3629193647:ℚ)/5000000000),((1486931037:ℚ)/2000000000),((6205875731:ℚ)/8850000000),((4844793111:ℚ)/6100000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1504823443:ℚ)/5000000000),((-2564929452010381566434042455612215015717200845511377:ℚ)/72203554687500000000000000000000000000000000000000000),((-3314660238425956338256847:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1475447757:ℚ)/2000000000),((7553504871:ℚ)/10000000000),((17637925327:ℚ)/25160000000),((8193504871:ℚ)/10325000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((30339229:ℚ)/125000000),((-691075619202113550744669212809862648841065018800487:ℚ)/19442046015625000000000000000000000000000000000000000),((-529965980999571801211367:ℚ)/2310400000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((7496087207:ℚ)/10000000000),((3895597733:ℚ)/5000000000),((29832319759:ℚ)/43200000000),((12646793199:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1655536611:ℚ)/10000000000),((-41913221238432508272372281974706814611205645979931071:ℚ)/1244160000000000000000000000000000000000000000000000000),((-13246287646233905114644767:ℚ)/57760000000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((966721923:ℚ)/1250000000),((9692394011:ℚ)/10000000000),((11513941153:ℚ)/20000000000),((1148043779:ℚ)/1200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-28064614415629999451593526649158297395074001328593379:ℚ)/1875000000000000000000000000000000000000000000000000000),((-458709:ℚ)/2000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9634958727:ℚ)/10000000000),((6746900229:ℚ)/5000000000),((113024545997:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1563943393701308526965938154267410631:ℚ)/538229145600000000000000000000000000000),((-458709:ℚ)/2000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC28
#check @N11Formalization.C450Source13GroupedC28.bound
#print axioms N11Formalization.C450Source13GroupedC28.valid0
#print axioms N11Formalization.C450Source13GroupedC28.valid1
#print axioms N11Formalization.C450Source13GroupedC28.valid2
#print axioms N11Formalization.C450Source13GroupedC28.valid3
#print axioms N11Formalization.C450Source13GroupedC28.valid4
#print axioms N11Formalization.C450Source13GroupedC28.valid5
#print axioms N11Formalization.C450Source13GroupedC28.valid6
#print axioms N11Formalization.C450Source13GroupedC28.valid7
#print axioms N11Formalization.C450Source13GroupedC28.valid8
#print axioms N11Formalization.C450Source13GroupedC28.valid9
#print axioms N11Formalization.C450Source13GroupedC28.valid10
#print axioms N11Formalization.C450Source13GroupedC28.valid11
#print axioms N11Formalization.C450Source13GroupedC28.valid12
#print axioms N11Formalization.C450Source13GroupedC28.valid13
#print axioms N11Formalization.C450Source13GroupedC28.valid14
#print axioms N11Formalization.C450Source13GroupedC28.bound
#print axioms N11Formalization.C450Source13GroupedC28.endpoint_checks
