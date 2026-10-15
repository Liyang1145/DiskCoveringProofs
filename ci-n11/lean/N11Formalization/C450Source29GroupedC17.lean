import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(0:ℚ),((1:ℚ)/16),((6028401427:ℚ)/10000000000),((1269251847:ℚ)/2000000000),((432:ℚ)/2575),((4853251847:ℚ)/19840000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((25575497:ℚ)/39062500),((-759357357202920145736597211470947:ℚ)/26677905273437500000000000000000000),((-464038665392514720501354563:ℚ)/1774387200000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((3134854343:ℚ)/5000000000),((6587049797:ℚ)/10000000000),((72:ℚ)/445),((24507049797:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6006619499:ℚ)/10000000000),((-1762916064867561731444220914329:ℚ)/68844628906250000000000000000000),((-4007167950074530881090167721:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((3255369469:ℚ)/5000000000),((6707357087:ℚ)/10000000000),((864:ℚ)/5435),((8209119029:ℚ)/35600000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2710024413:ℚ)/5000000000),((-3083173930510468440263148927483003:ℚ)/125426318652343750000000000000000000),((-4157800827326689655083860561:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6631159529:ℚ)/10000000000),((6827609851:ℚ)/10000000000),((432:ℚ)/2765),((24747609851:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5104576733:ℚ)/10000000000),((-6002617552496370648587636806779:ℚ)/258045008850097656250000000000000),((-4227238623554855292906294569:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((6751521547:ℚ)/10000000000),((6947810921:ℚ)/10000000000),((96:ℚ)/625),((24867810921:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2385197857:ℚ)/5000000000),((-524266465656371595467225766119:ℚ)/23841857910156250000000000000000),((-226128367811252933744810491:ℚ)/778240000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((6871828039:ℚ)/10000000000),((3533981467:ℚ)/5000000000),((108:ℚ)/715),((1388220163:ℚ)/6250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((882643443:ℚ)/2000000000),((-47428506986757956755345322372027:ℚ)/2284536718750000000000000000000000),((-1091350992048856842426174441:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((1748020461:ℚ)/2500000000),((143761367:ℚ)/200000000),((864:ℚ)/5815),((502161367:ℚ)/2288000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2013441817:ℚ)/5000000000),((-3006747066130078402659306224454387:ℚ)/153616967480468750000000000000000000),((-1773654187788212162839841:ℚ)/5914624000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((3556142803:ℚ)/5000000000),((3654064733:ℚ)/5000000000),((144:ℚ)/985),((12614064733:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((225123753:ℚ)/625000000),((-6877741113059909337977683987521:ℚ)/373309228515625000000000000000000),((-1125658816973052138102369241:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((3616220899:ℚ)/5000000000),((3774063627:ℚ)/5000000000),((216:ℚ)/1525),((12734063627:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3122750619:ℚ)/10000000000),((-177839800088942029311789339634803:ℚ)/11083056640625000000000000000000000),((-3418713174333388350871016603:ℚ)/11089920000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7472620563:ℚ)/10000000000),((4013838563:ℚ)/5000000000),((2:ℚ)/15),((12973838563:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((91671919:ℚ)/500000000),((-55282508713744733746007449:ℚ)/4687500000000000000000000000),((-19383471218591243:ℚ)/60800000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((994062451:ℚ)/1250000000),((4970754471:ℚ)/5000000000),((27:ℚ)/250),((13930754471:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((49670444744390303569460559951:ℚ)/48828125000000000000000000000000),((-66476503:ℚ)/204800000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((2466832153:ℚ)/2500000000),((550306969:ℚ)/400000000),((9:ℚ)/115),((1267106969:ℚ)/6400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((191697961230020597869723287899:ℚ)/9505468750000000000000000000000),((-66476503:ℚ)/204800000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC17
#check @N11Formalization.C450Source29GroupedC17.bound
#print axioms N11Formalization.C450Source29GroupedC17.valid0
#print axioms N11Formalization.C450Source29GroupedC17.valid1
#print axioms N11Formalization.C450Source29GroupedC17.valid2
#print axioms N11Formalization.C450Source29GroupedC17.valid3
#print axioms N11Formalization.C450Source29GroupedC17.valid4
#print axioms N11Formalization.C450Source29GroupedC17.valid5
#print axioms N11Formalization.C450Source29GroupedC17.valid6
#print axioms N11Formalization.C450Source29GroupedC17.valid7
#print axioms N11Formalization.C450Source29GroupedC17.valid8
#print axioms N11Formalization.C450Source29GroupedC17.valid9
#print axioms N11Formalization.C450Source29GroupedC17.valid10
#print axioms N11Formalization.C450Source29GroupedC17.valid11
#print axioms N11Formalization.C450Source29GroupedC17.bound
#print axioms N11Formalization.C450Source29GroupedC17.endpoint_checks
