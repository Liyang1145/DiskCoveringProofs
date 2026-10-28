import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((1157263279:ℚ)/2000000000),((633367357:ℚ)/1000000000),((4751789837:ℚ)/10680000000),((5777571499:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((282156827:ℚ)/400000000),((1361370711602104868865841:ℚ)/57031200000000000000000000),((-26161321401045635977179827:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((313231247:ℚ)/500000000),((6572601857:ℚ)/10000000000),((1259693741:ℚ)/2765000000),((59448212999:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((601844453:ℚ)/1000000000),((237353844423098851524792847535387:ℚ)/16382625000000000000000000000000000),((-2689963995029435950162388827:ℚ)/7393280000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((6503607077:ℚ)/10000000000),((6811434457:ℚ)/10000000000),((25910821231:ℚ)/57200000000),((8731434457:ℚ)/15800000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5438212669:ℚ)/10000000000),((17295750083207889613255381881441657:ℚ)/1258400000000000000000000000000000000),((-2717222883114482725262426027:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((210702809:ℚ)/312500000),((6930817837:ℚ)/10000000000),((832108427:ℚ)/1817187500),((61955724859:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4796213281:ℚ)/10000000000),((1987729746001094733584537004504917:ℚ)/198130224609375000000000000000000000),((-2753512329939209070382181587:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((1715474281:ℚ)/2500000000),((3525090349:ℚ)/5000000000),((6746422843:ℚ)/14775000000),((31395632443:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4443711033:ℚ)/10000000000),((1800012775557163660467673867259483:ℚ)/181917187500000000000000000000000000),((-36404150262923513018916417:ℚ)/97280000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((349064153:ℚ)/500000000),((7169524021:ℚ)/10000000000),((1367192459:ℚ)/3002500000),((63626668147:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((253936741:ℚ)/625000000),((1324586268967009922678626860451469:ℚ)/135225093750000000000000000000000000),((-2779750321970476525247264643:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((3550324359:ℚ)/5000000000),((7288848729:ℚ)/10000000000),((13850973077:ℚ)/30500000000),((64461941103:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((729034981:ℚ)/2000000000),((742124961768174936330265076683367:ℚ)/76250000000000000000000000000000000),((-8377851705284260814226876929:ℚ)/22179840000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((1443999011:ℚ)/2000000000),((7527445707:ℚ)/10000000000),((5611997033:ℚ)/12580000000),((66132119949:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((3175625133:ℚ)/10000000000),((4988627169461637394551264026560263:ℚ)/395641000000000000000000000000000000),((-441308511755118737036214899:ℚ)/1167360000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((3729316651:ℚ)/5000000000),((1553195587:ℚ)/2000000000),((14387949953:ℚ)/32400000000),((13560369109:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((77271127:ℚ)/400000000),((65811728123117139329785240616399291:ℚ)/5248800000000000000000000000000000000),((-186470710864321521:ℚ)/486400000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((7697204347:ℚ)/10000000000),((4836231043:ℚ)/5000000000),((29491613041:ℚ)/80000000000),((40573617301:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1011261126246178856948445781079251217:ℚ)/24000000000000000000000000000000000000),((-198163229:ℚ)/512000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((9603932003:ℚ)/10000000000),((6740029029:ℚ)/5000000000),((35211796009:ℚ)/110400000000),((53900203203:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((455351541000985361645458009:ℚ)/6094080000000000000000000000),((-198163229:ℚ)/512000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC23
#check @N11Formalization.C450Source22GroupedC23.bound
#print axioms N11Formalization.C450Source22GroupedC23.valid0
#print axioms N11Formalization.C450Source22GroupedC23.valid1
#print axioms N11Formalization.C450Source22GroupedC23.valid2
#print axioms N11Formalization.C450Source22GroupedC23.valid3
#print axioms N11Formalization.C450Source22GroupedC23.valid4
#print axioms N11Formalization.C450Source22GroupedC23.valid5
#print axioms N11Formalization.C450Source22GroupedC23.valid6
#print axioms N11Formalization.C450Source22GroupedC23.valid7
#print axioms N11Formalization.C450Source22GroupedC23.valid8
#print axioms N11Formalization.C450Source22GroupedC23.valid9
#print axioms N11Formalization.C450Source22GroupedC23.valid10
#print axioms N11Formalization.C450Source22GroupedC23.bound
#print axioms N11Formalization.C450Source22GroupedC23.endpoint_checks
