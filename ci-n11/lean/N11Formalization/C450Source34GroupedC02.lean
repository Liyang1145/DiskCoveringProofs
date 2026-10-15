import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((227779829:ℚ)/312500000),((7539532041:ℚ)/10000000000),((-18522596123:ℚ)/19840000000),((-1264458803:ℚ)/1579687500),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2870863763:ℚ)/10000000000),((248835650022332582120282054093085602519581:ℚ)/496531561045500000000000000000000000000000),((3167133732972176792196780411:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((7408290827:ℚ)/10000000000),((3829295613:ℚ)/5000000000),((-9439886839:ℚ)/10110000000),((-41298035789:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1125425689:ℚ)/5000000000),((9087696680128548545488712378110520665595569585280373857112479:ℚ)/18178698143994140625000000000000000000000000000000000000000000),((1099952237:ℚ)/1024000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((3763802671:ℚ)/5000000000),((987084559:ℚ)/1250000000),((-2449253677:ℚ)/2575000000),((-21066618697:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((138135979:ℚ)/1000000000),((2535461946216130791213738122444431865410021545352577200889:ℚ)/4930015509448242187500000000000000000000000000000000000000),((1099952237:ℚ)/1024000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((7766173709:ℚ)/10000000000),((8372729939:ℚ)/10000000000),((-21022189817:ℚ)/21360000000),((-3369478151:ℚ)/4400000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((2277281310942824432953458538044366797710412891022125067383:ℚ)/4217140400000000000000000000000000000000000000000000000000),((1099952237:ℚ)/1024000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((4121548117:ℚ)/5000000000),((9324465209:ℚ)/10000000000),(-1:ℚ),((-23570836819:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((88912252920317123443271639927873158071168098406442214561:ℚ)/159432300000000000000000000000000000000000000000000000000),((1099952237:ℚ)/1024000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((9196261509:ℚ)/10000000000),((1403368093:ℚ)/1250000000),(-1:ℚ),((-53813830563:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((113133948476247532620480274726290576714779411855293747939:ℚ)/200000000000000000000000000000000000000000000000000000000),((1099952237:ℚ)/1024000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((1110078153:ℚ)/1000000000),((15029853183:ℚ)/10000000000),(-1:ℚ),((-2238182357:ℚ)/3680000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((7359731161198523675508298546684503:ℚ)/12459008000000000000000000000000000),((1099952237:ℚ)/1024000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_3 node3_7
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_7
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6]
theorem packet_count : packets.length = 7 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC02
#check @N11Formalization.C450Source34GroupedC02.bound
#print axioms N11Formalization.C450Source34GroupedC02.valid0
#print axioms N11Formalization.C450Source34GroupedC02.valid1
#print axioms N11Formalization.C450Source34GroupedC02.valid2
#print axioms N11Formalization.C450Source34GroupedC02.valid3
#print axioms N11Formalization.C450Source34GroupedC02.valid4
#print axioms N11Formalization.C450Source34GroupedC02.valid5
#print axioms N11Formalization.C450Source34GroupedC02.valid6
#print axioms N11Formalization.C450Source34GroupedC02.bound
#print axioms N11Formalization.C450Source34GroupedC02.endpoint_checks
