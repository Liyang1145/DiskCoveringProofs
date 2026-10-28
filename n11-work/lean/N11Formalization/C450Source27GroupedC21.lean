import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/4),((5:ℚ)/16),((5795786303:ℚ)/10000000000),((611426793:ℚ)/1000000000),((9795786303:ℚ)/25750000000),((944226793:ℚ)/1984000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7034679763:ℚ)/10000000000),((65666649909243074200087398934056631:ℚ)/4142566198476800000000000000000000000),((-35117253989342371947435323:ℚ)/88719360000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((6036244471:ℚ)/10000000000),((794300243:ℚ)/1250000000),((10036244471:ℚ)/26700000000),((1210300243:ℚ)/2575000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3265180767:ℚ)/5000000000),((436461155844056309313715731840796136651182938265050859:ℚ)/29716268578720092773437500000000000000000000000000000000),((-18603154205801192458666241:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3138244233:ℚ)/5000000000),((1318870429:ℚ)/2000000000),((5138244233:ℚ)/13825000000),((661490143:ℚ)/1424000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5990817579:ℚ)/10000000000),((1558058961334010556021665840607795989347229693028065079:ℚ)/112632615142400000000000000000000000000000000000000000000),((-48408059084352615608729569:ℚ)/118292480000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((6516540851:ℚ)/10000000000),((3357132127:ℚ)/5000000000),((1168504539:ℚ)/3125000000),((5021132127:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((270261583:ℚ)/500000000),((11340538730575776147610824038812005165342338352231737:ℚ)/1207945550000000000000000000000000000000000000000000000),((-308782124797204334471847961:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((1327300277:ℚ)/2000000000),((1708534303:ℚ)/2500000000),((2127300277:ℚ)/5720000000),((2540534303:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5090172007:ℚ)/10000000000),((23461104716260624751213939237693610021209627396243943751:ℚ)/2527418518066406250000000000000000000000000000000000000000),((-77791115879061512631549081:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((844552639:ℚ)/1250000000),((6953972973:ℚ)/10000000000),((1344552639:ℚ)/3634375000),((10281972973:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4756335907:ℚ)/10000000000),((233687328101809516498169092013790171578925993053028522237381:ℚ)/25313227121811200000000000000000000000000000000000000000000000),((-3762246194363912795869998083:ℚ)/8871936000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((859537759:ℚ)/1250000000),((1768443341:ℚ)/2500000000),((453179253:ℚ)/1231250000),((2600443341:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((8592607:ℚ)/19531250),((110090233017866590685326695517402471721155041589118993877:ℚ)/11923441781899023437500000000000000000000000000000000000000),((-78962587149934854781761729:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((874518271:ℚ)/1250000000),((1828318689:ℚ)/2500000000),((1374518271:ℚ)/3812500000),((2660318689:ℚ)/5910000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2006607823:ℚ)/5000000000),((20513535860926966224764524360094608167915351691687992691:ℚ)/1600224352481250000000000000000000000000000000000000000000),((-237462128925458606956933067:ℚ)/554496000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((3617865391:ℚ)/5000000000),((1558384283:ℚ)/2000000000),((1872621797:ℚ)/5400000000),((2223984283:ℚ)/4880000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3108633597:ℚ)/10000000000),((2557939409036657254412854454196413152884195651399728771:ℚ)/132375319200000000000000000000000000000000000000000000000),((-10541451417838093:ℚ)/24320000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((3857264451:ℚ)/5000000000),((9703014621:ℚ)/10000000000),((5857264451:ℚ)/20000000000),((13031014621:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((23906438472307187464110953696730921:ℚ)/500000000000000000000000000000000000),((-459917719:ℚ)/1024000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9626081597:ℚ)/10000000000),((844749419:ℚ)/625000000),((4542027199:ℚ)/18400000000),((1052749419:ℚ)/2000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((15642819664922375132286251:ℚ)/169280000000000000000000000),((-459917719:ℚ)/1024000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC21
#check @N11Formalization.C450Source27GroupedC21.bound
#print axioms N11Formalization.C450Source27GroupedC21.valid0
#print axioms N11Formalization.C450Source27GroupedC21.valid1
#print axioms N11Formalization.C450Source27GroupedC21.valid2
#print axioms N11Formalization.C450Source27GroupedC21.valid3
#print axioms N11Formalization.C450Source27GroupedC21.valid4
#print axioms N11Formalization.C450Source27GroupedC21.valid5
#print axioms N11Formalization.C450Source27GroupedC21.valid6
#print axioms N11Formalization.C450Source27GroupedC21.valid7
#print axioms N11Formalization.C450Source27GroupedC21.valid8
#print axioms N11Formalization.C450Source27GroupedC21.valid9
#print axioms N11Formalization.C450Source27GroupedC21.valid10
#print axioms N11Formalization.C450Source27GroupedC21.bound
#print axioms N11Formalization.C450Source27GroupedC21.endpoint_checks
