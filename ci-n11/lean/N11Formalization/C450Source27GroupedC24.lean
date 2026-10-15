import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((701778977:ℚ)/1250000000),((308832693:ℚ)/500000000),((6912452839:ℚ)/13350000000),((412832693:ℚ)/620000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7396348697:ℚ)/10000000000),((-14456636320762648998462452829138193:ℚ)/198272531250000000000000000000000000),((-45413629229261721950869:ℚ)/108300000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6093956831:ℚ)/10000000000),((1283252531:ℚ)/2000000000),((58657697817:ℚ)/110600000000),((1699252531:ℚ)/2670000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((12508479:ℚ)/19531250),((-743070895839808637954980568282178181418723335157865327279:ℚ)/8455618850000000000000000000000000000000000000000000000000),((-247062671145813006889047:ℚ)/577600000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((1266714503:ℚ)/2000000000),((6536012949:ℚ)/10000000000),((12067001521:ℚ)/22500000000),((8616012949:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1464071519:ℚ)/2500000000),((-747417706006243362922093264202356620644452851265151783:ℚ)/7910156250000000000000000000000000000000000000000000000),((-18708844087594009550320981:ℚ)/43320000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((3226663037:ℚ)/5000000000),((6655729609:ℚ)/10000000000),((30586641259:ℚ)/57200000000),((8735729609:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5564758007:ℚ)/10000000000),((-10039566100640340010693628863551947535861609161256049063:ℚ)/106334800000000000000000000000000000000000000000000000000),((-6249073043405338902067887:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((51351921:ℚ)/78125000),((677541431:ℚ)/1000000000),((484463447:ℚ)/908593750),((885541431:ℚ)/1430000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5258960969:ℚ)/10000000000),((-55260203225343956526887956521663530274103122813747:ℚ)/586002225801348686218261718750000000000000000000000),((-62612530047379228457647:ℚ)/144400000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3346366819:ℚ)/5000000000),((3447534309:ℚ)/5000000000),((10474855911:ℚ)/19700000000),((4487534309:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1234052999:ℚ)/2500000000),((-1124672827870687843526671183472163795656883172498674417:ℚ)/11945895312500000000000000000000000000000000000000000000),((-4704616443695866554166261:ℚ)/10830000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6812390893:ℚ)/10000000000),((1753673499:ℚ)/2500000000),((63686736251:ℚ)/120100000000),((2273673499:ℚ)/3693750000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((574113211:ℚ)/1250000000),((-1017275956725442683365051301098781572297339547481026088173:ℚ)/10827022506250000000000000000000000000000000000000000000000),((-1178208832091485928479381:ℚ)/2707500000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((1733004781:ℚ)/2500000000),((1426858363:ℚ)/2000000000),((16131033467:ℚ)/30500000000),((1842858363:ℚ)/3002500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2111998867:ℚ)/5000000000),((-16621344195963103659389771418361137947685535163640260669:ℚ)/177328906250000000000000000000000000000000000000000000000),((-251765165497048330978663:ℚ)/577600000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1410323941:ℚ)/2000000000),((7373409841:ℚ)/10000000000),((13072267587:ℚ)/25160000000),((9453409841:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1911022333:ℚ)/5000000000),((-2189666155149458033259624229396758087830769176937785869:ℚ)/24885818900000000000000000000000000000000000000000000000),((-6266786356487894067622687:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7290743:ℚ)/10000000),((7612432067:ℚ)/10000000000),((22345067:ℚ)/43200000),((9692432067:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2862541323:ℚ)/10000000000),((-1634793217165022313596148645756116328843558983:ℚ)/18662400000000000000000000000000000000000000000),((-330908055863:ℚ)/760000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((7529770181:ℚ)/10000000000),((1904397651:ℚ)/2000000000),((68708391267:ℚ)/160000000000),((2320397651:ℚ)/3240000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1360517021:ℚ)/10000000000),((-1024025678794543695949154606565265431:ℚ)/32000000000000000000000000000000000000),((-335770107751721:ℚ)/760000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((4719678703:ℚ)/5000000000),((13333171963:ℚ)/10000000000),((13679250307:ℚ)/36800000000),((15413171963:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((14462203429398498500996099:ℚ)/677120000000000000000000000),((-7098919:ℚ)/16000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC24
#check @N11Formalization.C450Source27GroupedC24.bound
#print axioms N11Formalization.C450Source27GroupedC24.valid0
#print axioms N11Formalization.C450Source27GroupedC24.valid1
#print axioms N11Formalization.C450Source27GroupedC24.valid2
#print axioms N11Formalization.C450Source27GroupedC24.valid3
#print axioms N11Formalization.C450Source27GroupedC24.valid4
#print axioms N11Formalization.C450Source27GroupedC24.valid5
#print axioms N11Formalization.C450Source27GroupedC24.valid6
#print axioms N11Formalization.C450Source27GroupedC24.valid7
#print axioms N11Formalization.C450Source27GroupedC24.valid8
#print axioms N11Formalization.C450Source27GroupedC24.valid9
#print axioms N11Formalization.C450Source27GroupedC24.valid10
#print axioms N11Formalization.C450Source27GroupedC24.valid11
#print axioms N11Formalization.C450Source27GroupedC24.bound
#print axioms N11Formalization.C450Source27GroupedC24.endpoint_checks
