import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3597466489:ℚ)/5000000000),((930169051:ℚ)/1250000000),((-5231183357:ℚ)/6200000000),((-36207064357:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((655918229:ℚ)/2000000000),((14902052804449807518178742473132008131383:ℚ)/31033222565343750000000000000000000000000),((25757159288456337755145783:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((7314535961:ℚ)/10000000000),((1890175757:ℚ)/2500000000),((-10671230299:ℚ)/12637500000),((-73968967493:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1374746899:ℚ)/5000000000),((23212364128746205214719803570522571956123725678974433173497629:ℚ)/48476528383984375000000000000000000000000000000000000000000000),((103365719732580983717272167:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((1858526787:ℚ)/2500000000),((7799339699:ℚ)/10000000000),((-44355377893:ℚ)/51500000000),((-6293616077:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((209322157:ℚ)/1000000000),((89489298656016561312552968293040293438683901112923225269:ℚ)/182593167016601562500000000000000000000000000000000000000),((114655761:ℚ)/128000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7673161009:ℚ)/10000000000),((165527701:ℚ)/200000000),((-953893907:ℚ)/1068000000),((-78631093117:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((113536039776338629409892460000249711922832816289681724666020687:ℚ)/222361379011200000000000000000000000000000000000000000000000000),((114655761:ℚ)/128000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((8150956333:ℚ)/10000000000),((9229752321:ℚ)/10000000000),((-54368266247:ℚ)/57200000000),((-84842432329:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((113823204112038247996729321185542771492954580771777331477831019:ℚ)/208654790572800000000000000000000000000000000000000000000000000),((114655761:ℚ)/128000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((1821111279:ℚ)/2000000000),((2783640091:ℚ)/2500000000),(-1:ℚ),((-19450446627:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((7359526515489873156325570869005773956653940085705199971:ℚ)/12800000000000000000000000000000000000000000000000000000),((114655761:ℚ)/128000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((688257571:ℚ)/625000000),((7470097933:ℚ)/5000000000),(-1:ℚ),((-7627348423:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((391545073229510350157661882558643957:ℚ)/657018000000000000000000000000000000),((114655761:ℚ)/128000000)⟩
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
end N11Formalization.C450Source34GroupedC03
#check @N11Formalization.C450Source34GroupedC03.bound
#print axioms N11Formalization.C450Source34GroupedC03.valid0
#print axioms N11Formalization.C450Source34GroupedC03.valid1
#print axioms N11Formalization.C450Source34GroupedC03.valid2
#print axioms N11Formalization.C450Source34GroupedC03.valid3
#print axioms N11Formalization.C450Source34GroupedC03.valid4
#print axioms N11Formalization.C450Source34GroupedC03.valid5
#print axioms N11Formalization.C450Source34GroupedC03.valid6
#print axioms N11Formalization.C450Source34GroupedC03.bound
#print axioms N11Formalization.C450Source34GroupedC03.endpoint_checks
