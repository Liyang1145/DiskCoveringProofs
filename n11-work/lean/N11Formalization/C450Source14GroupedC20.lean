import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((6049522633:ℚ)/10000000000),((1313665499:ℚ)/2000000000),((8609522633:ℚ)/35600000000),((1729665499:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((812694091:ℚ)/1250000000),((7041923501047865507480630291684344537:ℚ)/241637899264000000000000000000000000000),((-1372398698746926828998679:ℚ)/9241600000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6525984147:ℚ)/10000000000),((6806401691:ℚ)/10000000000),((27257952441:ℚ)/110600000000),((2962133897:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5381036419:ℚ)/10000000000),((108160555476275093029230551697936877969931931257443092978619:ℚ)/4042234967268750000000000000000000000000000000000000000000000),((-35698883288455520582344599:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((3382069633:ℚ)/5000000000),((108209753:ℚ)/156250000),((1554023211:ℚ)/6250000000),((140709753:ℚ)/432031250),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((591763709:ℚ)/1250000000),((1855066698647080077597174848599650048226316492451:ℚ)/71999165415763854980468750000000000000000000000000),((-4442507487821137929993:ℚ)/28203125000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((6883200163:ℚ)/10000000000),((1761109403:ℚ)/2500000000),((28329600489:ℚ)/114400000000),((760369801:ℚ)/2343750000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2189027219:ℚ)/5000000000),((42069400113584955124771827833990089875874152385684348339:ℚ)/1645454764366149902343750000000000000000000000000000000000),((-2296129959704848276914711:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((3501125347:ℚ)/5000000000),((7103941057:ℚ)/10000000000),((4781125347:ℚ)/19225000000),((9183941057:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3992603497:ℚ)/10000000000),((1630208770109096206313296334692966134516941368790431202946931:ℚ)/64847324089762500000000000000000000000000000000000000000000000),((-37085011891824761226505071:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7061772233:ℚ)/10000000000),((1790860599:ℚ)/2500000000),((28865316699:ℚ)/116300000000),((2310860599:ℚ)/7209375000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((946516619:ℚ)/2500000000),((1058384155608207629848449379023388343619840561404996987813:ℚ)/42234857383016120910644531250000000000000000000000000000000),((-122557479852047306175941:ℚ)/760000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/16),((1:ℚ)/4),((712129137:ℚ)/1000000000),((7222941683:ℚ)/10000000000),((2904387411:ℚ)/11725000000),((9302941683:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1784104287:ℚ)/5000000000),((211052026841851974489022936196671441997020541951240897327667:ℚ)/8447435445992846679687500000000000000000000000000000000000000),((-37429912453199504196953031:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3590404081:ℚ)/5000000000),((1456487793:ℚ)/2000000000),((4870404081:ℚ)/19700000000),((27947579:ℚ)/87500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1668404319:ℚ)/5000000000),((1012053460654458051606999574923132440557133347806531:ℚ)/40623434448242187500000000000000000000000000000000000),((-1504093111740413552819471:ℚ)/9241600000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((7240322667:ℚ)/10000000000),((7341934291:ℚ)/10000000000),((29400968001:ℚ)/119150000000),((9421934291:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4826281:ℚ)/15625000),((68262038472750369467783372180936441465724590629636231066743913:ℚ)/2747399484402935156250000000000000000000000000000000000000000000),((-37774720065919525957707399:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((364991747:ℚ)/500000000),((1850356927:ℚ)/2500000000),((1478975241:ℚ)/6005000000),((2370356927:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2819863729:ℚ)/10000000000),((5766647567593261405875411893922740715963604415560125209687:ℚ)/232684921833571040630340576171875000000000000000000000000000),((-2371693089475906933793391:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((7359345033:ℚ)/10000000000),((7520408993:ℚ)/10000000000),((29758035099:ℚ)/122000000000),((9600408993:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1261619323:ℚ)/5000000000),((15710104446553529340085403325181808520800644595295229006113:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-38117367486102530568932271:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((934794861:ℚ)/1250000000),((3879175273:ℚ)/5000000000),((3764384583:ℚ)/15725000000),((4919175273:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((895775871:ℚ)/5000000000),((3261617388349804168418941096989286251106757296593788377569:ℚ)/128967988598632812500000000000000000000000000000000000000000),((-316310471495661:ℚ)/1900000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((771636261:ℚ)/1000000000),((7996266137:ℚ)/10000000000),((1027636261:ℚ)/4320000000),((10076266137:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1185474969870526927349115103300041258773172231933945329699:ℚ)/47244171817968750000000000000000000000000000000000000000000),((-1344177:ℚ)/8000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((1590867341:ℚ)/2000000000),((4949439409:ℚ)/5000000000),((6308602023:ℚ)/32000000000),((1996479803:ℚ)/5400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5465506265235986469521690663549307384710785325655121:ℚ)/184528125000000000000000000000000000000000000000000000),((-1344177:ℚ)/8000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((1971463391:ℚ)/2000000000),((13701943303:ℚ)/10000000000),((2483463391:ℚ)/14720000000),((15781943303:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((313603638297405369922852913459116632149:ℚ)/8464000000000000000000000000000000000000),((-1344177:ℚ)/8000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC20
#check @N11Formalization.C450Source14GroupedC20.bound
#print axioms N11Formalization.C450Source14GroupedC20.valid0
#print axioms N11Formalization.C450Source14GroupedC20.valid1
#print axioms N11Formalization.C450Source14GroupedC20.valid2
#print axioms N11Formalization.C450Source14GroupedC20.valid3
#print axioms N11Formalization.C450Source14GroupedC20.valid4
#print axioms N11Formalization.C450Source14GroupedC20.valid5
#print axioms N11Formalization.C450Source14GroupedC20.valid6
#print axioms N11Formalization.C450Source14GroupedC20.valid7
#print axioms N11Formalization.C450Source14GroupedC20.valid8
#print axioms N11Formalization.C450Source14GroupedC20.valid9
#print axioms N11Formalization.C450Source14GroupedC20.valid10
#print axioms N11Formalization.C450Source14GroupedC20.valid11
#print axioms N11Formalization.C450Source14GroupedC20.valid12
#print axioms N11Formalization.C450Source14GroupedC20.valid13
#print axioms N11Formalization.C450Source14GroupedC20.valid14
#print axioms N11Formalization.C450Source14GroupedC20.bound
#print axioms N11Formalization.C450Source14GroupedC20.endpoint_checks
