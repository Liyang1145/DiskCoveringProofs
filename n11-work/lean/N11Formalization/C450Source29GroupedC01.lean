import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((720109889:ℚ)/1000000000),((3689687501:ℚ)/5000000000),(-1:ℚ),((-1801929667:ℚ)/2003000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((1627155071:ℚ)/5000000000),((30792590212163918884862341513546884006631062380047:ℚ)/80360540270000000000000000000000000000000000000000),((11716375553749377707281:ℚ)/10000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1452116447:ℚ)/2000000000),((7438750003:ℚ)/10000000000),(-1:ℚ),((-3639549341:ℚ)/4044000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((93746533:ℚ)/312500000),((475200167269648211060637381266042771166885366119581307:ℚ)/1240037197200000000000000000000000000000000000000000000),((16990047436750854532830969:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3660031769:ℚ)/5000000000),((3749062501:ℚ)/5000000000),(-1:ℚ),((-9188095307:ℚ)/10205000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2722576483:ℚ)/10000000000),((10133921712167931509590944739258618523071354681499:ℚ)/26442311035156250000000000000000000000000000000000),((11815725664301496457281:ℚ)/10000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((922442857:ℚ)/1250000000),((3778750001:ℚ)/5000000000),(-1:ℚ),((-2319328571:ℚ)/2575000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((482898361:ℚ)/2000000000),((122700153190617975303557933243628273893729389652244053:ℚ)/320134863281250000000000000000000000000000000000000000),((11865670062839274582281:ℚ)/10000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((3719510123:ℚ)/5000000000),((3838125001:ℚ)/5000000000),(-1:ℚ),((-9366530369:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2061880123:ℚ)/10000000000),((697353578282819605341033459028554099838365512561126341:ℚ)/1803626014062500000000000000000000000000000000000000000),((1190153:ℚ)/1000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((7557969447:ℚ)/10000000000),((3897500001:ℚ)/5000000000),(-1:ℚ),((-19089908341:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1052182581:ℚ)/10000000000),((5886854121132944845453013238843306883732822004767578841:ℚ)/15227330400000000000000000000000000000000000000000000000),((1190153:ℚ)/1000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((7676911543:ℚ)/10000000000),((8270000003:ℚ)/10000000000),(-1:ℚ),((-19446734629:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((90522768128305427676219841209576481862945999722266075043:ℚ)/224579097600000000000000000000000000000000000000000000000),((1190153:ℚ)/1000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((407630799:ℚ)/500000000),((4610000001:ℚ)/5000000000),(-1:ℚ),((-1043692397:ℚ)/1296000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4261336478528712777582098280174160263224400127808891:ℚ)/10203667200000000000000000000000000000000000000000000),((1190153:ℚ)/1000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((182075531:ℚ)/200000000),((11120000003:ℚ)/10000000000),(-1:ℚ),((-474546593:ℚ)/640000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((133451562335940218658502958808887828197932359744471:ℚ)/307200000000000000000000000000000000000000000000000),((1190153:ℚ)/1000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((2201087063:ℚ)/2000000000),((14920000003:ℚ)/10000000000),(-1:ℚ),((-5886461189:ℚ)/8832000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((78496439370005794701140122170557827:ℚ)/172233326592000000000000000000000000),((1190153:ℚ)/1000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC01
#check @N11Formalization.C450Source29GroupedC01.bound
#print axioms N11Formalization.C450Source29GroupedC01.valid0
#print axioms N11Formalization.C450Source29GroupedC01.valid1
#print axioms N11Formalization.C450Source29GroupedC01.valid2
#print axioms N11Formalization.C450Source29GroupedC01.valid3
#print axioms N11Formalization.C450Source29GroupedC01.valid4
#print axioms N11Formalization.C450Source29GroupedC01.valid5
#print axioms N11Formalization.C450Source29GroupedC01.valid6
#print axioms N11Formalization.C450Source29GroupedC01.valid7
#print axioms N11Formalization.C450Source29GroupedC01.valid8
#print axioms N11Formalization.C450Source29GroupedC01.valid9
#print axioms N11Formalization.C450Source29GroupedC01.bound
#print axioms N11Formalization.C450Source29GroupedC01.endpoint_checks
