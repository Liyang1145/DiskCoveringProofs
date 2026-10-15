import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7032951511:ℚ)/10000000000),((1454878117:ℚ)/2000000000),((-3308634351:ℚ)/4960000000),((-55602466621:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((3887373783:ℚ)/10000000000),((1518026995188875881612052518719094100108509:ℚ)/3530891100768000000000000000000000000000000),((8738617496320870889126271:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((7153119087:ℚ)/10000000000),((3697169837:ℚ)/5000000000),((-2817169837:ℚ)/4212500000),((-56924309957:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1723159489:ℚ)/5000000000),((20792232230570055723627124038356375194642291656498203508313877:ℚ)/48476528383984375000000000000000000000000000000000000000000000),((8705130535308798646523919:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7273233459:ℚ)/10000000000),((751424469:ℚ)/1000000000),((-1726273407:ℚ)/2575000000),((-58245568049:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2943035279:ℚ)/10000000000),((127962688936595323592798417685675346998711486522865760808009:ℚ)/298979193487329101562500000000000000000000000000000000000000),((456365362846505510041149:ℚ)/760000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((3696648791:ℚ)/5000000000),((763410803:ℚ)/1000000000),((-1762232409:ℚ)/2622500000),((-29783136701:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2337600239:ℚ)/10000000000),((16569081583933822589691095355363942115529281792888721289302367:ℚ)/38787429628450000000000000000000000000000000000000000000000000),((2158382116204840223988831:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((3756657099:ℚ)/5000000000),((4056593437:ℚ)/5000000000),((-3176593437:ℚ)/4450000000),((-30443228089:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),((75590263:ℚ)/500000000),((4183283273627736695415369047643161374165244664840960924081249:ℚ)/9265057458800000000000000000000000000000000000000000000000000),((2147268145619802136440951:ℚ)/3610000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((7992953847:ℚ)/10000000000),((2267473603:ℚ)/2500000000),((-5482420809:ℚ)/7150000000),((-66162492317:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((11087856608858664877132615266246052100409232213383815999895839:ℚ)/23183865619200000000000000000000000000000000000000000000000000),((4740453:ℚ)/8000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8950581263:ℚ)/10000000000),((10979457819:ℚ)/10000000000),((-9219457819:ℚ)/10800000000),((-76696393893:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((141481608330911784234261420706349:ℚ)/270000000000000000000000000000000),((4740453:ℚ)/8000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((2715362947:ℚ)/2500000000),((14790649951:ℚ)/10000000000),((-39091949853:ℚ)/40000000000),((-24428992417:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((24724469259275812484226597:ℚ)/40000000000000000000000000),((4740453:ℚ)/8000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_4 node4_8
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_8
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7]
theorem packet_count : packets.length = 8 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC05
#check @N11Formalization.C450Source35GroupedC05.bound
#print axioms N11Formalization.C450Source35GroupedC05.valid0
#print axioms N11Formalization.C450Source35GroupedC05.valid1
#print axioms N11Formalization.C450Source35GroupedC05.valid2
#print axioms N11Formalization.C450Source35GroupedC05.valid3
#print axioms N11Formalization.C450Source35GroupedC05.valid4
#print axioms N11Formalization.C450Source35GroupedC05.valid5
#print axioms N11Formalization.C450Source35GroupedC05.valid6
#print axioms N11Formalization.C450Source35GroupedC05.valid7
#print axioms N11Formalization.C450Source35GroupedC05.bound
#print axioms N11Formalization.C450Source35GroupedC05.endpoint_checks
