import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7154394833:ℚ)/10000000000),((1850830151:ℚ)/2500000000),((-18620791963:ℚ)/24800000000),((-15863184499:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1720673511:ℚ)/5000000000),((29919436364358135407038021968274696687031:ℚ)/62066445130687500000000000000000000000000),((2786259597440026833456531041:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((363719529:ℚ)/500000000),((752305499:ℚ)/1000000000),((-7603971487:ℚ)/10110000000),((-811158587:ℚ)/1287500000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((73444549:ℚ)/250000000),((204672709475825177387596821197079259383680484476559459883:ℚ)/426063237749862670898437500000000000000000000000000000000),((6964929013214945538589329:ℚ)/9241600000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((7394339669:ℚ)/10000000000),((1552483491:ℚ)/2000000000),((-15830285383:ℚ)/20600000000),((-16583019007:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((466334679:ℚ)/2000000000),((1210551563214287513894386452005376582091368454513193812943:ℚ)/2465007754724121093750000000000000000000000000000000000000),((2783645683424412194006998009:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((305364321:ℚ)/400000000),((128761989:ℚ)/156250000),((-1333905857:ℚ)/1668750000),((-692092963:ℚ)/1144000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((56811120017024822323834811915936235286117284665052018721:ℚ)/111180689505600000000000000000000000000000000000000000000),((192066457:ℚ)/256000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((8113186869:ℚ)/10000000000),((9196278213:ℚ)/10000000000),((-8890146979:ℚ)/10400000000),((-18739560607:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((7356643640469454398015059023786955404537740877990921304501:ℚ)/13472029350000000000000000000000000000000000000000000000000),((192066457:ℚ)/256000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((9069894407:ℚ)/10000000000),((11104139669:ℚ)/10000000000),((-122593815697:ℚ)/129600000000),((-21609683221:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5505939394445984930691785861235973473114918114089422511821:ℚ)/9112500000000000000000000000000000000000000000000000000000),((192066457:ℚ)/256000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((5489728907:ℚ)/5000000000),((14913345031:ℚ)/10000000000),(-1:ℚ),((-13669186721:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((333731:ℚ)/500000),((192066457:ℚ)/256000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_3 node3_7
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_7
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6]
theorem packet_count : packets.length = 7 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC04
#check @N11Formalization.C450Source36GroupedC04.bound
#print axioms N11Formalization.C450Source36GroupedC04.valid0
#print axioms N11Formalization.C450Source36GroupedC04.valid1
#print axioms N11Formalization.C450Source36GroupedC04.valid2
#print axioms N11Formalization.C450Source36GroupedC04.valid3
#print axioms N11Formalization.C450Source36GroupedC04.valid4
#print axioms N11Formalization.C450Source36GroupedC04.valid5
#print axioms N11Formalization.C450Source36GroupedC04.valid6
#print axioms N11Formalization.C450Source36GroupedC04.bound
#print axioms N11Formalization.C450Source36GroupedC04.endpoint_checks
