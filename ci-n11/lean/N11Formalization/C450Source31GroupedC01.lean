import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7274345417:ℚ)/10000000000),((7518750003:ℚ)/10000000000),(-1:ℚ),((-5994345417:ℚ)/6740000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((293798717:ℚ)/1000000000),((819595766999492537228172257335949710325647996497209579:ℚ)/1913637650000000000000000000000000000000000000000000000),((17594409708493339937858731:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((3696671573:ℚ)/5000000000),((3818750001:ℚ)/5000000000),(-1:ℚ),((-9170014719:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2337341403:ℚ)/10000000000),((2923892360741221375121066490559676661870490698653930293:ℚ)/6829543750000000000000000000000000000000000000000000000),((612693:ℚ)/500000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((7512331707:ℚ)/10000000000),((3937500001:ℚ)/5000000000),(-1:ℚ),((-6232331707:ℚ)/7120000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((760182459:ℚ)/5000000000),((245040102559167787503395128988023178004954849441821041:ℚ)/563975200000000000000000000000000000000000000000000000),((612693:ℚ)/500000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((3875141647:ℚ)/5000000000),((8350000003:ℚ)/10000000000),(-1:ℚ),((-9705424941:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((4161685599362161726611995331837915827403333759871701823:ℚ)/9357462400000000000000000000000000000000000000000000000),((612693:ℚ)/500000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((2056524059:ℚ)/2500000000),((4650000001:ℚ)/5000000000),(-1:ℚ),((-578841353:ℚ)/720000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((9909773630821502752202435053509456517248888652033:ℚ)/21600000000000000000000000000000000000000000000000),((612693:ℚ)/500000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((9177435489:ℚ)/10000000000),((11200000003:ℚ)/10000000000),(-1:ℚ),((-23692306467:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6062562094871505912643203473829423015614686885783951961:ℚ)/12800000000000000000000000000000000000000000000000000000),((612693:ℚ)/500000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((692459343:ℚ)/625000000),((7500000001:ℚ)/5000000000),(-1:ℚ),((-612459343:ℚ)/920000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((96483927241847284756851032641607:ℚ)/194672000000000000000000000000000),((612693:ℚ)/500000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_3 node3_7
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_7
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6]
theorem packet_count : packets.length = 7 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC01
#check @N11Formalization.C450Source31GroupedC01.bound
#print axioms N11Formalization.C450Source31GroupedC01.valid0
#print axioms N11Formalization.C450Source31GroupedC01.valid1
#print axioms N11Formalization.C450Source31GroupedC01.valid2
#print axioms N11Formalization.C450Source31GroupedC01.valid3
#print axioms N11Formalization.C450Source31GroupedC01.valid4
#print axioms N11Formalization.C450Source31GroupedC01.valid5
#print axioms N11Formalization.C450Source31GroupedC01.valid6
#print axioms N11Formalization.C450Source31GroupedC01.bound
#print axioms N11Formalization.C450Source31GroupedC01.endpoint_checks
