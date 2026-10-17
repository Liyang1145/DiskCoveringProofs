import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((6055256247:ℚ)/10000000000),((3283255163:ℚ)/5000000000),((15408931243:ℚ)/35600000000),((3563255163:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6489079081:ℚ)/10000000000),((1281719828174495923378131:ℚ)/633680000000000000000000000),((-4604962688810771607137864621:ℚ)/44359680000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6530594049:ℚ)/10000000000),((1701032571:ℚ)/2500000000),((49554158343:ℚ)/110600000000),((1841032571:ℚ)/3337500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5369189421:ℚ)/10000000000),((170545201094265629608778466129994831:ℚ)/183485400000000000000000000000000000000),((-4660173809367911512385264669:ℚ)/44359680000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((1692061381:ℚ)/2500000000),((3461468611:ℚ)/5000000000),((12804429667:ℚ)/28125000000),((3741468611:ℚ)/6912500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2361122677:ℚ)/5000000000),((1766722903472898960423917232961039:ℚ)/3955078125000000000000000000000000000),((-97669339034192391530901703:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((344353371:ℚ)/500000000),((279293599:ℚ)/400000000),((2602473597:ℚ)/5672500000),((33521511:ℚ)/62500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((873207301:ℚ)/2000000000),((35273462646301430340970733390349:ℚ)/160886281250000000000000000000000000),((-11755481944630030775902229:ℚ)/110899200000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((1389295493:ℚ)/2000000000),((7041742267:ℚ)/10000000000),((10493068451:ℚ)/22880000000),((7601742267:ℚ)/14181250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((4177349559:ℚ)/10000000000),((7699984667537458890956239647227:ℚ)/40268800000000000000000000000000000),((-62789958041880799494093127:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((3502943463:ℚ)/5000000000),((7101144109:ℚ)/10000000000),((8813534747:ℚ)/19225000000),((7661144109:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3980277641:ℚ)/10000000000),((456002778320129044694745519955409:ℚ)/2772004687500000000000000000000000000),((-1179078869692630425472032461:ℚ)/11089920000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((353264791:ℚ)/500000000),((7160545513:ℚ)/10000000000),((2664853537:ℚ)/5815000000),((2573515171:ℚ)/4806250000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((58960991:ℚ)/156250000),((4702668588461048764262154678307:ℚ)/33814225000000000000000000000000000),((-3936165546948518137411663:ℚ)/36966400000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/16),((1:ℚ)/2),((44529401:ℚ)/62500000),((902493311:ℚ)/1250000000),((335705807:ℚ)/732812500),((972493311:ℚ)/1817187500),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3555330471:ℚ)/10000000000),((7403877666795797587345169033717:ℚ)/64441699218750000000000000000000000),((-61595005038806447589423:ℚ)/577600000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3592055979:ℚ)/5000000000),((1455869409:ℚ)/2000000000),((9021463951:ℚ)/19700000000),((1567869409:ℚ)/2931250000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1661755237:ℚ)/5000000000),((89189609685285780584798415696271:ℚ)/970225000000000000000000000000000000),((-1184402167931498526927053429:ℚ)/11089920000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((724351923:ℚ)/1000000000),((1467749439:ℚ)/2000000000),((5454463461:ℚ)/11915000000),((1579749439:ℚ)/2955000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((768738471:ℚ)/2500000000),((149372302613724094428549923769859:ℚ)/2129508375000000000000000000000000000),((-47447355120965013683016101:ℚ)/443596800000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3651462993:ℚ)/5000000000),((3699073473:ℚ)/5000000000),((27480240951:ℚ)/60050000000),((3979073473:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2805210459:ℚ)/10000000000),((223183882413512730209535787656873:ℚ)/4507503125000000000000000000000000000),((-1187969227226725639827224381:ℚ)/11089920000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((7362332239:ℚ)/10000000000),((1879236323:ℚ)/2500000000),((55376325673:ℚ)/122000000000),((2019236323:ℚ)/3753125000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((626861601:ℚ)/2500000000),((13538875393823443682803420191625577:ℚ)/74420000000000000000000000000000000000),((-1586344287781277458802518783:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1870285821:ℚ)/2500000000),((2423293:ℚ)/3125000),((14052000747:ℚ)/31450000000),((2598293:ℚ)/4765625),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((44271853:ℚ)/250000000),((1071954126982552962732111595456013:ℚ)/2472756250000000000000000000000000000),((-298336778088969869730349829:ℚ)/2772480000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7718759839:ℚ)/10000000000),((1998031123:ℚ)/2500000000),((57871318873:ℚ)/129600000000),((2138031123:ℚ)/3931250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((30193995196031015630338146646994641:ℚ)/83980800000000000000000000000000000000),((-22104377:ℚ)/204800000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((3978184777:ℚ)/5000000000),((9892670981:ℚ)/10000000000),((29767293439:ℚ)/80000000000),((10452670981:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((78940649837381135679626569421428387:ℚ)/24000000000000000000000000000000000000),((-22104377:ℚ)/204800000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((1971411913:ℚ)/2000000000),((13693312399:ℚ)/10000000000),((14567883391:ℚ)/44160000000),((14253312399:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6011570649860098261170539:ℚ)/975052800000000000000000000),((-22104377:ℚ)/204800000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC24
#check @N11Formalization.C450EighthGroupedC24.bound
#print axioms N11Formalization.C450EighthGroupedC24.valid0
#print axioms N11Formalization.C450EighthGroupedC24.valid1
#print axioms N11Formalization.C450EighthGroupedC24.valid2
#print axioms N11Formalization.C450EighthGroupedC24.valid3
#print axioms N11Formalization.C450EighthGroupedC24.valid4
#print axioms N11Formalization.C450EighthGroupedC24.valid5
#print axioms N11Formalization.C450EighthGroupedC24.valid6
#print axioms N11Formalization.C450EighthGroupedC24.valid7
#print axioms N11Formalization.C450EighthGroupedC24.valid8
#print axioms N11Formalization.C450EighthGroupedC24.valid9
#print axioms N11Formalization.C450EighthGroupedC24.valid10
#print axioms N11Formalization.C450EighthGroupedC24.valid11
#print axioms N11Formalization.C450EighthGroupedC24.valid12
#print axioms N11Formalization.C450EighthGroupedC24.valid13
#print axioms N11Formalization.C450EighthGroupedC24.valid14
#print axioms N11Formalization.C450EighthGroupedC24.valid15
#print axioms N11Formalization.C450EighthGroupedC24.bound
#print axioms N11Formalization.C450EighthGroupedC24.endpoint_checks
