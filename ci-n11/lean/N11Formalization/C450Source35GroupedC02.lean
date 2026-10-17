import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7321978593:ℚ)/10000000000),((7576002031:ℚ)/10000000000),((-18504006093:ℚ)/19840000000),((-40373850151:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((271319013:ℚ)/1000000000),((29010915700664083368652695406403875264403:ℚ)/55170173449500000000000000000000000000000),((555023936633363721968739:ℚ)/512000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((7441352403:ℚ)/10000000000),((7695080317:ℚ)/10000000000),((-6287080317:ℚ)/6740000000),((-41209466821:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2046837379:ℚ)/10000000000),((3177680744297695472807927207694868178541271404203602857623829:ℚ)/6059566047998046875000000000000000000000000000000000000000000),((5556813:ℚ)/5120000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((7560703023:ℚ)/10000000000),((495825107:ℚ)/625000000),((-1223475321:ℚ)/1287500000),((-42044921161:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1017360997:ℚ)/10000000000),((2366710671960346861227043371845628896892249210321457850569:ℚ)/4382236008398437500000000000000000000000000000000000000000),((5556813:ℚ)/5120000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((3899669847:ℚ)/5000000000),((4204660111:ℚ)/5000000000),((-3500660111:ℚ)/3560000000),((-21857688929:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((657888856183628985207344841949513115083389479581844097495769:ℚ)/1158132182350000000000000000000000000000000000000000000000000),((5556813:ℚ)/5120000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((1655277009:ℚ)/2000000000),((4680581283:ℚ)/5000000000),(-1:ℚ),((-9410939063:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((666392387005849183649379723811695405789685640775712709:ℚ)/1133740800000000000000000000000000000000000000000000000),((5556813:ℚ)/5120000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((2307438079:ℚ)/2500000000),((450551799:ℚ)/400000000),(-1:ℚ),((-13432066553:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1863736733583147973099395697863536013333327025248846713:ℚ)/3125000000000000000000000000000000000000000000000000000),((5556813:ℚ)/5120000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((11134560359:ℚ)/10000000000),((15066882579:ℚ)/10000000000),(-1:ℚ),((-22353974171:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((7783800327115911958678322476680590897:ℚ)/12459008000000000000000000000000000000),((5556813:ℚ)/5120000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_3 node3_7
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_7
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6]
theorem packet_count : packets.length = 7 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC02
#check @N11Formalization.C450Source35GroupedC02.bound
#print axioms N11Formalization.C450Source35GroupedC02.valid0
#print axioms N11Formalization.C450Source35GroupedC02.valid1
#print axioms N11Formalization.C450Source35GroupedC02.valid2
#print axioms N11Formalization.C450Source35GroupedC02.valid3
#print axioms N11Formalization.C450Source35GroupedC02.valid4
#print axioms N11Formalization.C450Source35GroupedC02.valid5
#print axioms N11Formalization.C450Source35GroupedC02.valid6
#print axioms N11Formalization.C450Source35GroupedC02.bound
#print axioms N11Formalization.C450Source35GroupedC02.endpoint_checks
