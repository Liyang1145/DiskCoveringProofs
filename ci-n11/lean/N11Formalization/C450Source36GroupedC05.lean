import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((1763958829:ℚ)/2500000000),((1460105621:ℚ)/2000000000),((-3292316863:ℚ)/4960000000),((-4601182373:ℚ)/8425000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((475893099:ℚ)/1250000000),((1026685800814675877812244995504615353648579:ℚ)/2353927400512000000000000000000000000000000),((2224334118342659476445339:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((3588045887:ℚ)/5000000000),((46378437:ℚ)/62500000),((-105135311:ℚ)/157968750),((-28268504757:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1677852369:ℚ)/5000000000),((3953476843335168633767070368228632580267445854007270251004791:ℚ)/9089349071997070312500000000000000000000000000000000000000000),((8863027680667927799855451:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7296291631:ℚ)/10000000000),((1885131237:ℚ)/2500000000),((-4295393711:ℚ)/6437500000),((-57859207941:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1418285163:ℚ)/5000000000),((64859137905624242881701961578070539214626949952249870659821:ℚ)/149489596743664550781250000000000000000000000000000000000000),((1858529658225119106659001:ℚ)/3040000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((7416438037:ℚ)/10000000000),((957556967:ℚ)/1250000000),((-2192670901:ℚ)/3278125000),((-19726939469:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1101152761:ℚ)/5000000000),((67163013923960995485103070005141030879094267544668584613131341:ℚ)/155149718513800000000000000000000000000000000000000000000000000),((35152448930980332959766851:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((753653391:ℚ)/1000000000),((8139781381:ℚ)/10000000000),((-18979344143:ℚ)/26700000000),((-6050187301:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),((258649569:ℚ)/2000000000),((51114794011257453515947889513451428359670955125583297527143:ℚ)/111180689505600000000000000000000000000000000000000000000000),((349735505134817349675899:ℚ)/577600000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((2004115869:ℚ)/2500000000),((9096893813:ℚ)/10000000000),((-21850681439:ℚ)/28600000000),((-16445274559:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((797574142675914080153596249142669034148409770825767547261613:ℚ)/1630115551350000000000000000000000000000000000000000000000000),((4830727:ℚ)/8000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8974566217:ℚ)/10000000000),((11007032693:ℚ)/10000000000),((-27581098079:ℚ)/32400000000),((-76320228387:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((39391756171860497892727340997342767:ℚ)/72900000000000000000000000000000000),((4830727:ℚ)/8000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((21261937:ℚ)/19531250),((14818896109:ℚ)/10000000000),((-39016688327:ℚ)/40000000000),((-190131307:ℚ)/431250000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((259909429520140014741349917:ℚ)/400000000000000000000000000),((4830727:ℚ)/8000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_4 node4_8
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_8
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7]
theorem packet_count : packets.length = 8 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC05
#check @N11Formalization.C450Source36GroupedC05.bound
#print axioms N11Formalization.C450Source36GroupedC05.valid0
#print axioms N11Formalization.C450Source36GroupedC05.valid1
#print axioms N11Formalization.C450Source36GroupedC05.valid2
#print axioms N11Formalization.C450Source36GroupedC05.valid3
#print axioms N11Formalization.C450Source36GroupedC05.valid4
#print axioms N11Formalization.C450Source36GroupedC05.valid5
#print axioms N11Formalization.C450Source36GroupedC05.valid6
#print axioms N11Formalization.C450Source36GroupedC05.valid7
#print axioms N11Formalization.C450Source36GroupedC05.bound
#print axioms N11Formalization.C450Source36GroupedC05.endpoint_checks
