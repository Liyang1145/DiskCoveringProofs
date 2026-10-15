import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((3469386691:ℚ)/5000000000),((7176091779:ℚ)/10000000000),((-57817009569:ℚ)/99200000000),((-2381386691:ℚ)/5055000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((420226651:ℚ)/1000000000),((941982436373755991321211826160539491:ℚ)/2460160000000000000000000000000000000),((111274068080091915330010979:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1411833213:ℚ)/2000000000),((361809929:ℚ)/500000000),((-2923909219:ℚ)/5055000000),((-976633213:ℚ)/2041000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((94883327:ℚ)/250000000),((6716963320300423352763031662447:ℚ)/17745156250000000000000000000000),((17648517173586952089387171:ℚ)/36966400000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((7119339003:ℚ)/10000000000),((1824072909:ℚ)/2500000000),((-14784801999:ℚ)/25512500000),((-4943339003:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((357555583:ℚ)/1000000000),((9470218542089264156591338456075437:ℚ)/25034140625000000000000000000000000),((439248583745759062197998931:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7179496929:ℚ)/10000000000),((7356371333:ℚ)/10000000000),((-59800084663:ℚ)/103000000000),((-5003496929:ℚ)/10395000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1671036191:ℚ)/5000000000),((501382012161464089745053652519693957:ℚ)/1326125000000000000000000000000000000),((437269118778305771458619019:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1447928053:ℚ)/2000000000),((3708219021:ℚ)/5000000000),((-305357669:ℚ)/525000000),((-1012728053:ℚ)/2098000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((618354429:ℚ)/2000000000),((309986374175750345776994535883:ℚ)/820312500000000000000000000000),((17410981282866231235350131:ℚ)/36966400000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((7299769419:ℚ)/10000000000),((1507306783:ℚ)/2000000000),((-12356374613:ℚ)/20980000000),((-5123769419:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((705043383:ℚ)/2500000000),((20981110683089068271797891929749137:ℚ)/55020050000000000000000000000000000),((433264821289251579857715699:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((741998673:ℚ)/1000000000),((3888292353:ℚ)/5000000000),((-10737071961:ℚ)/17800000000),((-524398673:ℚ)/1106000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2180828093:ℚ)/10000000000),((3842483028089970284434989065812479:ℚ)/9901250000000000000000000000000000),((4292000188498202349599211:ℚ)/9241600000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((3830133729:ℚ)/5000000000),((8016463481:ℚ)/10000000000),((-67061098291:ℚ)/110600000000),((-2742133729:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((169200074291807937881905670932981559:ℚ)/436870000000000000000000000000000000),((58586821:ℚ)/128000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((1975090103:ℚ)/2500000000),((4487283111:ℚ)/5000000000),((-3527283111:ℚ)/5200000000),((-1431090103:ℚ)/3240000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2883721352402994091677993848111547:ℚ)/6760000000000000000000000000000000),((58586821:ℚ)/128000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((2214797749:ℚ)/2500000000),((10886111749:ℚ)/10000000000),((-98627229239:ℚ)/129600000000),((-1670797749:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((18236744728155105494178941391027589:ℚ)/38880000000000000000000000000000000),((58586821:ℚ)/128000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((5385884787:ℚ)/5000000000),((14699614963:ℚ)/10000000000),((-140575764593:ℚ)/160000000000),((-4297884787:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((356768141023557344914509917:ℚ)/640000000000000000000000000),((58586821:ℚ)/128000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source35 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC06
#check @N11Formalization.C450Source35GroupedC06.bound
#print axioms N11Formalization.C450Source35GroupedC06.valid0
#print axioms N11Formalization.C450Source35GroupedC06.valid1
#print axioms N11Formalization.C450Source35GroupedC06.valid2
#print axioms N11Formalization.C450Source35GroupedC06.valid3
#print axioms N11Formalization.C450Source35GroupedC06.valid4
#print axioms N11Formalization.C450Source35GroupedC06.valid5
#print axioms N11Formalization.C450Source35GroupedC06.valid6
#print axioms N11Formalization.C450Source35GroupedC06.valid7
#print axioms N11Formalization.C450Source35GroupedC06.valid8
#print axioms N11Formalization.C450Source35GroupedC06.valid9
#print axioms N11Formalization.C450Source35GroupedC06.valid10
#print axioms N11Formalization.C450Source35GroupedC06.bound
#print axioms N11Formalization.C450Source35GroupedC06.endpoint_checks
