import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/16),((3:ℚ)/8),((2791522251:ℚ)/5000000000),((2960815017:ℚ)/5000000000),((4839522251:ℚ)/10300000000),((14162445051:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((116516091:ℚ)/156250000),((-3139425028478629260929002643466382402255994620627650826301:ℚ)/9819113600000000000000000000000000000000000000000000000000),((-169746307179070563635242403:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((5825129051:ℚ)/10000000000),((1540831059:ℚ)/2500000000),((3307043017:ℚ)/7120000000),((7262493177:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1743695473:ℚ)/2500000000),((-93543457126771034145527397109681005912687011787691414649:ℚ)/296791696166992187500000000000000000000000000000000000000),((-42345205022310045801873387:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((303343927:ℚ)/500000000),((314202929:ℚ)/500000000),((508143927:ℚ)/1087000000),((490202929:ℚ)/890000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((807966409:ℚ)/1250000000),((-1517399850245834347986214682913385517268981142463497311:ℚ)/4789383143750000000000000000000000000000000000000000000),((-1708040369805960752031507:ℚ)/4620800000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3093819501:ℚ)/5000000000),((6404723087:ℚ)/10000000000),((734545643:ℚ)/1580000000),((29774169261:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1548775171:ℚ)/2500000000),((-389791137535206653493373136005985033024410130383130367187:ℚ)/1238584896691894531250000000000000000000000000000000000000),((-682112267563990188986114963:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((3154164343:ℚ)/5000000000),((6525321407:ℚ)/10000000000),((1734054781:ℚ)/3750000000),((30135964221:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5916110997:ℚ)/10000000000),((-3873103972242276589629086952341310351504820595266739671:ℚ)/12386160424804687500000000000000000000000000000000000000),((-680861559427564810835979123:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((3214475647:ℚ)/5000000000),((6645856941:ℚ)/10000000000),((36800529:ℚ)/80000000),((10165856941:ℚ)/18750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5625184797:ℚ)/10000000000),((-12804100236709077893137972534573462721021432999499563117:ℚ)/41198730468750000000000000000000000000000000000000000000),((-679464240697876409797305387:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((6549510271:ℚ)/10000000000),((845791607:ℚ)/1250000000),((10645510271:ℚ)/23260000000),((3857374821:ℚ)/7150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5320327473:ℚ)/10000000000),((-496842426068328948185157992109712392549503857151403442973287:ℚ)/1608352444420150000000000000000000000000000000000000000000000),((-10592508027044255360584723:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6670008829:ℚ)/10000000000),((1721688027:ℚ)/2500000000),((10766008829:ℚ)/23640000000),((7805064081:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4998953259:ℚ)/10000000000),((-4834753074745520747802964286043641350797552157617852537329:ℚ)/15747555096300000000000000000000000000000000000000000000000),((-42264410451080361939204283:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((3395224983:ℚ)/5000000000),((7127431503:ℚ)/10000000000),((5443224983:ℚ)/12200000000),((10647431503:ℚ)/19700000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4657605513:ℚ)/10000000000),((-397099273916389427526254019118084203458722879856829911419693:ℚ)/1321335844350000000000000000000000000000000000000000000000000),((-665792045247123988623725843:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((7031171003:ℚ)/10000000000),((7608220779:ℚ)/10000000000),((3709057001:ℚ)/8640000000),((33384662337:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((243346891:ℚ)/625000000),((-1445172137646146209565969870669235757790777093859040864459:ℚ)/4999880908800000000000000000000000000000000000000000000000),((-84713718231369573:ℚ)/243200000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((3756017983:ℚ)/5000000000),((2381451189:ℚ)/2500000000),((5804017983:ℚ)/16000000000),((3261451189:ℚ)/5400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((12183457:ℚ)/80000000),((-511922399138241272650687845895173123077086570368533951159:ℚ)/2073600000000000000000000000000000000000000000000000000000),((-2320877603916987:ℚ)/6400000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9429848863:ℚ)/10000000000),((6673165211:ℚ)/5000000000),((13525848863:ℚ)/44160000000),((25299495633:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-85482330497629622910031305560896722158413359435449692237:ℚ)/403671859200000000000000000000000000000000000000000000000),((-9350513:ℚ)/25600000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC22
#check @N11Formalization.C450Source34GroupedC22.bound
#print axioms N11Formalization.C450Source34GroupedC22.valid0
#print axioms N11Formalization.C450Source34GroupedC22.valid1
#print axioms N11Formalization.C450Source34GroupedC22.valid2
#print axioms N11Formalization.C450Source34GroupedC22.valid3
#print axioms N11Formalization.C450Source34GroupedC22.valid4
#print axioms N11Formalization.C450Source34GroupedC22.valid5
#print axioms N11Formalization.C450Source34GroupedC22.valid6
#print axioms N11Formalization.C450Source34GroupedC22.valid7
#print axioms N11Formalization.C450Source34GroupedC22.valid8
#print axioms N11Formalization.C450Source34GroupedC22.valid9
#print axioms N11Formalization.C450Source34GroupedC22.valid10
#print axioms N11Formalization.C450Source34GroupedC22.valid11
#print axioms N11Formalization.C450Source34GroupedC22.bound
#print axioms N11Formalization.C450Source34GroupedC22.endpoint_checks
