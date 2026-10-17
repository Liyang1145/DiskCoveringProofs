import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((6166879273:ℚ)/10000000000),((6685584783:ℚ)/10000000000),((971471739:ℚ)/35600000000),((16:ℚ)/155),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1560497667:ℚ)/2500000000),((276988562548335120001716631213:ℚ)/4719490220000000000000000000000),((-20611136276935419:ℚ)/194560000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((6644247509:ℚ)/10000000000),((692401309:ℚ)/1000000000),((267598691:ℚ)/11060000000),((128:ℚ)/1335),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2534608841:ℚ)/5000000000),((495596125219499673952672787350939187595509:ℚ)/8731227529300500000000000000000000000000000),((-22659620283363327:ℚ)/194560000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((1376561749:ℚ)/2000000000),((3521601797:ℚ)/5000000000),((1278398203:ℚ)/56250000000),((256:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2189634547:ℚ)/5000000000),((5351716238342403560674517210389795041910393:ℚ)/95550380419921875000000000000000000000000000),((-4736666994994047:ℚ)/38912000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((1400412461:ℚ)/2000000000),((7162379387:ℚ)/10000000000),((2437620613:ℚ)/114400000000),((512:ℚ)/5625),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((249577569:ℚ)/625000000),((85847592485200129075552693434938967818951:ℚ)/1540012500000000000000000000000000000000000),((-254685012730557:ℚ)/2048000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((1780324759:ℚ)/2500000000),((1820385299:ℚ)/2500000000),((579614701:ℚ)/29075000000),((64:ℚ)/715),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3568179697:ℚ)/10000000000),((257262116035243691049922686733173981693599:ℚ)/4634990317714453125000000000000000000000000),((-6176686306795077:ℚ)/48640000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7240519769:ℚ)/10000000000),((7400689699:ℚ)/10000000000),((2199310301:ℚ)/118200000000),((512:ℚ)/5815),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3087966601:ℚ)/10000000000),((253136026510686460080540964775698336845877603:ℚ)/4578601644249225000000000000000000000000000000),((-25218345594292107:ℚ)/194560000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7359725281:ℚ)/10000000000),((7519825531:ℚ)/10000000000),((2080174469:ℚ)/120100000000),((256:ℚ)/2955),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((504246759:ℚ)/2000000000),((615116583807782517270793369545603582563608693:ℚ)/11165539831330162500000000000000000000000000000),((-25729880645003043:ℚ)/194560000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((74789163:ℚ)/100000000),((7638949289:ℚ)/10000000000),((1961050711:ℚ)/122000000000),((512:ℚ)/6005),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((223428901:ℚ)/1250000000),((1769895295123109794211296816731790478850298361:ℚ)/32229880596605000000000000000000000000000000000),((-262413535033089:ℚ)/1945600000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((1899523377:ℚ)/2500000000),((8115334257:ℚ)/10000000000),((494888581:ℚ)/43200000000),((128:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((55998293:ℚ)/2500000000),((14580158421023679214459495903732790864897:ℚ)/264750638400000000000000000000000000000000),((-6688191773952531:ℚ)/48640000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((4037338231:ℚ)/5000000000),((500979433:ℚ)/500000000),((-20979433:ℚ)/6480000000),((32:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((540334589326835360200792226437:ℚ)/9730975341796875000000000000000),((-17605887:ℚ)/128000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((9979498983:ℚ)/10000000000),((3456302367:ℚ)/2500000000),((-1056302367:ℚ)/40000000000),((8:ℚ)/125),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1223722183801599:ℚ)/20000000000000000),((-17605887:ℚ)/128000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC16
#check @N11Formalization.C450Source17GroupedC16.bound
#print axioms N11Formalization.C450Source17GroupedC16.valid0
#print axioms N11Formalization.C450Source17GroupedC16.valid1
#print axioms N11Formalization.C450Source17GroupedC16.valid2
#print axioms N11Formalization.C450Source17GroupedC16.valid3
#print axioms N11Formalization.C450Source17GroupedC16.valid4
#print axioms N11Formalization.C450Source17GroupedC16.valid5
#print axioms N11Formalization.C450Source17GroupedC16.valid6
#print axioms N11Formalization.C450Source17GroupedC16.valid7
#print axioms N11Formalization.C450Source17GroupedC16.valid8
#print axioms N11Formalization.C450Source17GroupedC16.valid9
#print axioms N11Formalization.C450Source17GroupedC16.valid10
#print axioms N11Formalization.C450Source17GroupedC16.bound
#print axioms N11Formalization.C450Source17GroupedC16.endpoint_checks
