import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((6177497441:ℚ)/10000000000),((6485584193:ℚ)/10000000000),((1514415807:ℚ)/51500000000),((10462502559:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((24872183:ℚ)/40000000),((384802325105661753652075294209434311767349:ℚ)/2589103874048000000000000000000000000000000),((-3548968481747839996395744383:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((6418269333:ℚ)/10000000000),((336292611:ℚ)/500000000),((63707389:ℚ)/2670000000),((10221730667:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5651484239:ℚ)/10000000000),((279724170621559725790734862596176978431850348760676763277331:ℚ)/1901841189038085937500000000000000000000000000000000000000000),((-11237609680445224893238898581:ℚ)/44359680000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6658803907:ℚ)/10000000000),((1369182489:ℚ)/2000000000),((230817511:ℚ)/10870000000),((9981196093:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5029625127:ℚ)/10000000000),((434338085975428014209369584554155244756963111307160294040415087:ℚ)/2998690258899600000000000000000000000000000000000000000000000000),((-3943046147723165513372801207:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1694747543:ℚ)/2500000000),((1741481733:ℚ)/2500000000),((36931181:ℚ)/1975000000),((2465252457:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2345534659:ℚ)/5000000000),((7064120960876231537022890179653780089330004298750864015929:ℚ)/48924103419329833984375000000000000000000000000000000000000),((-252608966120437221597045807:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((3449563111:ℚ)/5000000000),((1417179609:ℚ)/2000000000),((182820391:ℚ)/11250000000),((4870436889:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4328362011:ℚ)/10000000000),((1761191154213257569833224075517295453545989872367821853071:ℚ)/12230448693750000000000000000000000000000000000000000000000),((-1035129118079443632128695503:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((7019214659:ℚ)/10000000000),((7205827991:ℚ)/10000000000),((794172009:ℚ)/57200000000),((1068976149:ℚ)/12500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((983696937:ℚ)/2500000000),((35863470709090082090797728764929012176097296996751010456333:ℚ)/249621582031250000000000000000000000000000000000000000000000),((-4239367187387853856463929783:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7139257909:ℚ)/10000000000),((293028753:ℚ)/400000000),((26971247:ℚ)/2326000000),((9500742091:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((437487869:ℚ)/1250000000),((453731839315504102044734362943829671546338774603484801071528803:ℚ)/3164153390226400000000000000000000000000000000000000000000000000),((-4338297464680757488476467783:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7259258233:ℚ)/10000000000),((744557247:ℚ)/1000000000),((55442753:ℚ)/5910000000),((9380741767:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((751444679:ℚ)/2500000000),((13657129703037174126471302767334527602016408836199372938083031:ℚ)/95387534255192187500000000000000000000000000000000000000000000),((-4437309039007351918573427727:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((461201109:ℚ)/625000000),((1537035053:ℚ)/2000000000),((62964947:ℚ)/12200000000),((578798891:ℚ)/7387500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1208140101:ℚ)/5000000000),((449535030315873613853626937339221909736285836305064330169:ℚ)/3125438188439941406250000000000000000000000000000000000000),((-53160978886955581792073749:ℚ)/173280000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((1523804421:ℚ)/2000000000),((8164032619:ℚ)/10000000000),((-164032619:ℚ)/61000000000),((1804195579:ℚ)/24400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3293507037733928284553742076378845550284708098867594203:ℚ)/22698100000000000000000000000000000000000000000000000000),((-326806717:ℚ)/1024000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((8098220087:ℚ)/10000000000),((2015324509:ℚ)/2000000000),((-138441503:ℚ)/4320000000),((105454073:ℚ)/1600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2214682418942267399629661342721762926723517618592769:ℚ)/14400000000000000000000000000000000000000000000000000),((-326806717:ℚ)/1024000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((1251373171:ℚ)/1250000000),((13891369847:ℚ)/10000000000),((-5891369847:ℚ)/80000000000),((828626829:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((353961155509581920094398072581274551:ℚ)/2000000000000000000000000000000000000),((-326806717:ℚ)/1024000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC15
#check @N11Formalization.C450Source27GroupedC15.bound
#print axioms N11Formalization.C450Source27GroupedC15.valid0
#print axioms N11Formalization.C450Source27GroupedC15.valid1
#print axioms N11Formalization.C450Source27GroupedC15.valid2
#print axioms N11Formalization.C450Source27GroupedC15.valid3
#print axioms N11Formalization.C450Source27GroupedC15.valid4
#print axioms N11Formalization.C450Source27GroupedC15.valid5
#print axioms N11Formalization.C450Source27GroupedC15.valid6
#print axioms N11Formalization.C450Source27GroupedC15.valid7
#print axioms N11Formalization.C450Source27GroupedC15.valid8
#print axioms N11Formalization.C450Source27GroupedC15.valid9
#print axioms N11Formalization.C450Source27GroupedC15.valid10
#print axioms N11Formalization.C450Source27GroupedC15.valid11
#print axioms N11Formalization.C450Source27GroupedC15.bound
#print axioms N11Formalization.C450Source27GroupedC15.endpoint_checks
