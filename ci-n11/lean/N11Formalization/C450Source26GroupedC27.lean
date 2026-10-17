import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5469825411:ℚ)/10000000000),((1206559837:ℚ)/2000000000),((2335275137:ℚ)/3560000000),((16472158207:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3837031133:ℚ)/5000000000),((-1875186897862940810353487317987931:ℚ)/11279504000000000000000000000000000),((-120250684529288423277099:ℚ)/295731200000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1189576203:ℚ)/2000000000),((3135878937:ℚ)/5000000000),((1496776203:ℚ)/2212000000),((42494668307:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6719392867:ℚ)/10000000000),((-12833431651397506266383932926715784855335262904476427:ℚ)/67644950800000000000000000000000000000000000000000000),((-2242625934519718347083497:ℚ)/5544960000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((6186749957:ℚ)/10000000000),((319559997:ℚ)/500000000),((7722749957:ℚ)/11250000000),((4315159967:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6197115079:ℚ)/10000000000),((-594669066510831549698535043882835593558081684214184239:ℚ)/2966308593750000000000000000000000000000000000000000000),((-22363015167958390982017:ℚ)/55449600000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6306149461:ℚ)/10000000000),((3255309411:ℚ)/5000000000),((7842149461:ℚ)/11440000000),((43808403521:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1480312629:ℚ)/2500000000),((-170320386284197470230259551317571353485967652677056679:ℚ)/850678400000000000000000000000000000000000000000000000),((-2227865694946081416195073:ℚ)/5544960000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6425527219:ℚ)/10000000000),((6630015671:ℚ)/10000000000),((7961527219:ℚ)/11630000000),((88930172381:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5633626937:ℚ)/10000000000),((-1474306902088228072046401806903192742346584890127143257:ℚ)/7373614439062500000000000000000000000000000000000000000),((-2958986361515652923753411:ℚ)/7393280000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((1636221077:ℚ)/2500000000),((668970617:ℚ)/1000000000),((288603011:ℚ)/418750000),((8958676787:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5332314009:ℚ)/10000000000),((-70502659085816925459682744845534431152626072629497:ℚ)/344195938110351562500000000000000000000000000000000),((-29544205422376978619619:ℚ)/73932800000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6604555419:ℚ)/10000000000),((6749391559:ℚ)/10000000000),((2713518473:ℚ)/3940000000),((90243307149:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5175772463:ℚ)/10000000000),((-19555408300171323423702165207763211854431383693750793:ℚ)/95567162500000000000000000000000000000000000000000000),((-2948511426446498618372451:ℚ)/7393280000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1332844347:ℚ)/2000000000),((1717186873:ℚ)/2500000000),((1640044347:ℚ)/2402000000),((7629685201:ℚ)/9850000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2507408013:ℚ)/5000000000),((-17266901908586861174149561198035022325254871232124563:ℚ)/86616180050000000000000000000000000000000000000000000),((-183451476692734977021859:ℚ)/462080000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((6783540441:ℚ)/10000000000),((1747021103:ℚ)/2500000000),((8319540441:ℚ)/12200000000),((23217232133:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4677808591:ℚ)/10000000000),((-2258801883609462781496762039114269143407041860504279881:ℚ)/11349050000000000000000000000000000000000000000000000000),((-182685136684620964797939:ℚ)/462080000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6902841311:ℚ)/10000000000),((7226704689:ℚ)/10000000000),((8438841311:ℚ)/12580000000),((95493751579:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4316693183:ℚ)/10000000000),((-588960418995232817816066885358444424404131225532786711:ℚ)/3110727362500000000000000000000000000000000000000000000),((-8685363279058934763632473:ℚ)/22179840000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7141392799:ℚ)/10000000000),((7465258833:ℚ)/10000000000),((8677392799:ℚ)/12960000000),((98117847163:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1745850691:ℚ)/5000000000),((-95224978258285680366082383770307152486357373526482973:ℚ)/503884800000000000000000000000000000000000000000000000),((-8606477166373187671170457:ℚ)/22179840000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((5765533:ℚ)/7812500),((9371880467:ℚ)/10000000000),((6965533:ℚ)/12500000),((119090685137:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2412623513:ℚ)/10000000000),((-225177222776654331004099096383818810037653759:ℚ)/2288818359375000000000000000000000000000000000),((-2293434327231:ℚ)/5937500000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9286097957:ℚ)/10000000000),((13179637153:ℚ)/10000000000),((10822097957:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-8483711134606419800601241:ℚ)/243763200000000000000000000),((-24761673:ℚ)/64000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC27
#check @N11Formalization.C450Source26GroupedC27.bound
#print axioms N11Formalization.C450Source26GroupedC27.valid0
#print axioms N11Formalization.C450Source26GroupedC27.valid1
#print axioms N11Formalization.C450Source26GroupedC27.valid2
#print axioms N11Formalization.C450Source26GroupedC27.valid3
#print axioms N11Formalization.C450Source26GroupedC27.valid4
#print axioms N11Formalization.C450Source26GroupedC27.valid5
#print axioms N11Formalization.C450Source26GroupedC27.valid6
#print axioms N11Formalization.C450Source26GroupedC27.valid7
#print axioms N11Formalization.C450Source26GroupedC27.valid8
#print axioms N11Formalization.C450Source26GroupedC27.valid9
#print axioms N11Formalization.C450Source26GroupedC27.valid10
#print axioms N11Formalization.C450Source26GroupedC27.valid11
#print axioms N11Formalization.C450Source26GroupedC27.valid12
#print axioms N11Formalization.C450Source26GroupedC27.bound
#print axioms N11Formalization.C450Source26GroupedC27.endpoint_checks
