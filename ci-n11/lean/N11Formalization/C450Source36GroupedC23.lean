import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/8),((7:ℚ)/16),((545834477:ℚ)/1000000000),((5802836627:ℚ)/10000000000),((2725503431:ℚ)/5150000000),((63019856389:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3847898017:ℚ)/5000000000),((-350256479292995431410059390812479512694670815810301610045849:ℚ)/942634905600000000000000000000000000000000000000000000000000),((-1451726496204736222571818099:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((1425176351:ℚ)/2500000000),((6044855073:ℚ)/10000000000),((6995529053:ℚ)/13350000000),((64713985511:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3612969559:ℚ)/5000000000),((-83891088040484647829772520735421419148793908765443539717253:ℚ)/227936022656250000000000000000000000000000000000000000000000),((-75851679273663858903160121:ℚ)/194560000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((2971355117:ℚ)/5000000000),((1541435647:ℚ)/2500000000),((14354065351:ℚ)/27175000000),((5463349843:ℚ)/8900000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3365157429:ℚ)/5000000000),((-893646725659271928146059010593862399953117648963558290901:ℚ)/2394691571875000000000000000000000000000000000000000000000),((-90376332083485629567985979:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6063591317:ℚ)/10000000000),((392909671:ℚ)/625000000),((29070773951:ℚ)/55300000000),((4150367697:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((647090921:ℚ)/1000000000),((-3144467892436690348602635196931354761481686941417507729:ℚ)/8466888942229747772216796875000000000000000000000000000),((-5624763096865241178165121:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((1546099317:ℚ)/2500000000),((1601823867:ℚ)/2500000000),((7358297951:ℚ)/14062500000),((2401823867:ℚ)/3950000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1550610763:ℚ)/2500000000),((-2503081050732579642141614861605261900609314994829203:ℚ)/6770860290527343750000000000000000000000000000000000),((-89596094525292039408355459:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((6305132021:ℚ)/10000000000),((6527968459:ℚ)/10000000000),((29795396063:ℚ)/57200000000),((22698593071:ℚ)/37500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5923648719:ℚ)/10000000000),((-8673965782016252171249894073231727870703497755048318714697:ℚ)/23565673828125000000000000000000000000000000000000000000000),((-1426816178317985598314927011:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((3212899621:ℚ)/5000000000),((1329715427:ℚ)/2000000000),((15078698863:ℚ)/29075000000),((13788007989:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5632956671:ℚ)/10000000000),((-1450597472600318353547081065296350446723200623089968706037:ℚ)/3957355916800000000000000000000000000000000000000000000000),((-56791028411463632375009299:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((818300293:ℚ)/1250000000),((1692281173:ℚ)/2500000000),((3814900879:ℚ)/7387500000),((17445968211:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1065676649:ℚ)/2000000000),((-4143598718406641058349435234740088648100194238653242731989:ℚ)/11348453472619628906250000000000000000000000000000000000000),((-88276027718200741179020899:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((1666736129:ℚ)/2500000000),((7010048207:ℚ)/10000000000),((7720208387:ℚ)/15250000000),((71470337449:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((100147169:ℚ)/200000000),((-337216731710929480007569952162199237682421590473478960290383:ℚ)/944394699825000000000000000000000000000000000000000000000000),((-1386190731019433040262955419:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((1381571557:ℚ)/2000000000),((149825623:ℚ)/200000000),((6320714671:ℚ)/12960000000),((1496779361:ℚ)/2440000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((430088973:ℚ)/1000000000),((-1260862646020134518942090382037430207363520889126887649:ℚ)/3677092200000000000000000000000000000000000000000000000),((-531986988912560173549099:ℚ)/1478656000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((7389072109:ℚ)/10000000000),((4705103327:ℚ)/5000000000),((33047216327:ℚ)/80000000000),((14711907763:ℚ)/21600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((590370713:ℚ)/2500000000),((-26583531232177085445046183431042755648445643493459242889:ℚ)/94478400000000000000000000000000000000000000000000000000),((-356298184732596529:ℚ)/972800000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((9307941331:ℚ)/10000000000),((13232288749:ℚ)/10000000000),((38803823993:ℚ)/110400000000),((115026021243:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-51980965669106530625289969954852647239113984579933251485967:ℚ)/220800000000000000000000000000000000000000000000000000000000),((-95041979:ℚ)/256000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC23
#check @N11Formalization.C450Source36GroupedC23.bound
#print axioms N11Formalization.C450Source36GroupedC23.valid0
#print axioms N11Formalization.C450Source36GroupedC23.valid1
#print axioms N11Formalization.C450Source36GroupedC23.valid2
#print axioms N11Formalization.C450Source36GroupedC23.valid3
#print axioms N11Formalization.C450Source36GroupedC23.valid4
#print axioms N11Formalization.C450Source36GroupedC23.valid5
#print axioms N11Formalization.C450Source36GroupedC23.valid6
#print axioms N11Formalization.C450Source36GroupedC23.valid7
#print axioms N11Formalization.C450Source36GroupedC23.valid8
#print axioms N11Formalization.C450Source36GroupedC23.valid9
#print axioms N11Formalization.C450Source36GroupedC23.valid10
#print axioms N11Formalization.C450Source36GroupedC23.valid11
#print axioms N11Formalization.C450Source36GroupedC23.bound
#print axioms N11Formalization.C450Source36GroupedC23.endpoint_checks
