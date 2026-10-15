import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((18175301:ℚ)/31250000),((6364635979:ℚ)/10000000000),((26575301:ℚ)/66750000),((26133907937:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3496632989:ℚ)/5000000000),((3328311363198949141:ℚ)/92824218750000000000),((-4299272666942827366075023:ℚ)/12160000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3147481131:ℚ)/5000000000),((82547397:ℚ)/125000000),((4491481131:ℚ)/11060000000),((335642191:ℚ)/667500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2973786517:ℚ)/5000000000),((506990338584459464267573234255819:ℚ)/19113062500000000000000000000000000),((-13222285794244808784163:ℚ)/36100000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((3267096889:ℚ)/5000000000),((1680831821:ℚ)/2500000000),((4611096889:ℚ)/11250000000),((6802495463:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((107198441:ℚ)/200000000),((119561134751316123973489848848520836948299524461599103:ℚ)/5308354467773437500000000000000000000000000000000000000),((-5379980343736496339998637:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((6653765211:ℚ)/10000000000),((1368567293:ℚ)/2000000000),((9341765211:ℚ)/22880000000),((5513701879:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5043362219:ℚ)/10000000000),((26094212920912282558591261884837650222753185505310770183:ℚ)/1166500854492187500000000000000000000000000000000000000000),((-3464805128233441755610093:ℚ)/9241600000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((3386654543:ℚ)/5000000000),((696232061:ℚ)/1000000000),((4730654543:ℚ)/11630000000),((2792696183:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((588447127:ℚ)/1250000000),((200088859860476830763980249644506908924136853334309757219:ℚ)/8989072131325000000000000000000000000000000000000000000000),((-871539380563858199468397:ℚ)/2310400000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((430801673:ℚ)/625000000),((7081780941:ℚ)/10000000000),((598801673:ℚ)/1477500000),((28285342823:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4348081091:ℚ)/10000000000),((198432621088582551870032737718814049165736408509379758406563:ℚ)/8942581336424267578125000000000000000000000000000000000000000),((-87681125580077767802168717:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7012319539:ℚ)/10000000000),((7201218601:ℚ)/10000000000),((9700319539:ℚ)/24020000000),((28643655803:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((989595957:ℚ)/2500000000),((10309197913650145709528147386048350942729013104887260988870021:ℚ)/465230826305423437500000000000000000000000000000000000000000000),((-88201700666576919395972757:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((3565894297:ℚ)/5000000000),((7320634661:ℚ)/10000000000),((4909894297:ℚ)/12200000000),((29001903983:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((882113457:ℚ)/2500000000),((27907069918831749502724855568529494837637117732604971554001:ℚ)/1258979710804882812500000000000000000000000000000000000000000),((-88715672534416761384828797:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1450247011:ℚ)/2000000000),((377970297:ℚ)/500000000),((1987847011:ℚ)/5032000000),((1485910891:ℚ)/3050000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1520616123:ℚ)/5000000000),((110485168941984212651634435293261806379254953009413041253:ℚ)/4384911612353515625000000000000000000000000000000000000000),((-222038597838497525848613:ℚ)/577600000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((1498012867:ℚ)/2000000000),((1559620421:ℚ)/2000000000),((2035612867:ℚ)/5184000000),((6086861263:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1702952027:ℚ)/10000000000),((1123624331557433339991367487789541847167206030563594091:ℚ)/44465102887500000000000000000000000000000000000000000000),((-9525473525786401:ℚ)/24320000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((7728815047:ℚ)/10000000000),((9705614481:ℚ)/10000000000),((10416815047:ℚ)/32000000000),((36156843443:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2223358442047467883560859388623543:ℚ)/40000000000000000000000000000000000),((-6324669:ℚ)/16000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9636669451:ℚ)/10000000000),((540576483:ℚ)/400000000),((12324669451:ℚ)/44160000000),((1903329449:ℚ)/3200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((926746762884395422429079:ℚ)/10156800000000000000000000),((-6324669:ℚ)/16000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC22
#check @N11Formalization.C450Source23GroupedC22.bound
#print axioms N11Formalization.C450Source23GroupedC22.valid0
#print axioms N11Formalization.C450Source23GroupedC22.valid1
#print axioms N11Formalization.C450Source23GroupedC22.valid2
#print axioms N11Formalization.C450Source23GroupedC22.valid3
#print axioms N11Formalization.C450Source23GroupedC22.valid4
#print axioms N11Formalization.C450Source23GroupedC22.valid5
#print axioms N11Formalization.C450Source23GroupedC22.valid6
#print axioms N11Formalization.C450Source23GroupedC22.valid7
#print axioms N11Formalization.C450Source23GroupedC22.valid8
#print axioms N11Formalization.C450Source23GroupedC22.valid9
#print axioms N11Formalization.C450Source23GroupedC22.valid10
#print axioms N11Formalization.C450Source23GroupedC22.valid11
#print axioms N11Formalization.C450Source23GroupedC22.bound
#print axioms N11Formalization.C450Source23GroupedC22.endpoint_checks
