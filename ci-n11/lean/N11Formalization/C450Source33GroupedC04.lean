import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3537755277:ℚ)/5000000000),((3657267983:ℚ)/5000000000),((-37624483779:ℚ)/49600000000),((-8053265831:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((747371287:ℚ)/2000000000),((10651541270698566894235916480407212043943:ℚ)/24826578052275000000000000000000000000000),((2683034848522596641198616931:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((7195293411:ℚ)/10000000000),((7434107153:ℚ)/10000000000),((-76803392989:ℚ)/101100000000),((-16465880233:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1639059249:ℚ)/5000000000),((97251656705268857624782266981427215270379061258629861427203:ℚ)/227233726799926757812500000000000000000000000000000000000000),((10734363572479930070375812419:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7315037683:ℚ)/10000000000),((3776824147:ℚ)/5000000000),((-39178713911:ℚ)/51500000000),((-16825113049:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1373530601:ℚ)/5000000000),((199482266429228741475932252853280508297210994648867256913:ℚ)/467154989823951721191406250000000000000000000000000000000),((10736226483172909244478505571:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((7434745501:ℚ)/10000000000),((3836580507:ℚ)/5000000000),((-39955546591:ℚ)/52450000000),((-17184236503:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1044587803:ℚ)/5000000000),((619824641921805853756397086713893992179971655302171332094239:ℚ)/1454528611066875000000000000000000000000000000000000000000000),((10723158171028118311977769539:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((188860471:ℚ)/250000000),((4075478169:ℚ)/5000000000),((-43061216197:ℚ)/53400000000),((-438581413:ℚ)/715000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),((1095766921:ℚ)/10000000000),((816751021362628681677189373004217605764921953367101509:ℚ)/1809581534921875000000000000000000000000000000000000000),((6687814626021478466422299:ℚ)/9241600000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((8032802261:ℚ)/10000000000),((22763891:ℚ)/25000000),((-246330583:ℚ)/286000000),((-18978406783:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((155816462706609907068607579242825204277519651438141220072293:ℚ)/326023110270000000000000000000000000000000000000000000000000),((148085589:ℚ)/204800000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8988368319:ℚ)/10000000000),((11012121141:ℚ)/10000000000),((-123317574833:ℚ)/129600000000),((-21845104957:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((316658932749348059770559496629823868788575208184246410367:ℚ)/607500000000000000000000000000000000000000000000000000000),((148085589:ℚ)/204800000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10896308241:ℚ)/10000000000),((7409905661:ℚ)/5000000000),(-1:ℚ),((-1198648901:ℚ)/2400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((11217:ℚ)/20000),((148085589:ℚ)/204800000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
private theorem node0_2 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_4 node4_8
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_8
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7]
theorem packet_count : packets.length = 8 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC04
#check @N11Formalization.C450Source33GroupedC04.bound
#print axioms N11Formalization.C450Source33GroupedC04.valid0
#print axioms N11Formalization.C450Source33GroupedC04.valid1
#print axioms N11Formalization.C450Source33GroupedC04.valid2
#print axioms N11Formalization.C450Source33GroupedC04.valid3
#print axioms N11Formalization.C450Source33GroupedC04.valid4
#print axioms N11Formalization.C450Source33GroupedC04.valid5
#print axioms N11Formalization.C450Source33GroupedC04.valid6
#print axioms N11Formalization.C450Source33GroupedC04.valid7
#print axioms N11Formalization.C450Source33GroupedC04.bound
#print axioms N11Formalization.C450Source33GroupedC04.endpoint_checks
