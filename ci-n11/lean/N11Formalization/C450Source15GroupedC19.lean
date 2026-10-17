import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((303527529:ℚ)/500000000),((6590031933:ℚ)/10000000000),((511527529:ℚ)/2670000000),((28730095799:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((806963121:ℚ)/1250000000),((662794379579941724972310656857233486102293:ℚ)/17397928747008000000000000000000000000000000),((-2169370259328778168239072257:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6547296593:ℚ)/10000000000),((136564399:ℚ)/200000000),((1529613799:ℚ)/7900000000),((588893197:ℚ)/2136000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5326066473:ℚ)/10000000000),((4519445230424579656548785807431377557943261290206984639:ℚ)/126711692035200000000000000000000000000000000000000000000),((-911586785891056542106713:ℚ)/5914624000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((1696394791:ℚ)/2500000000),((6947296457:ℚ)/10000000000),((912131597:ℚ)/4687500000),((29801889371:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1167963973:ℚ)/2500000000),((376988248504210101686268111192092856177554865464713922077:ℚ)/10871509950000000000000000000000000000000000000000000000000),((-2333726551871794055813340937:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((6904700531:ℚ)/10000000000),((3533181037:ℚ)/5000000000),((11064700531:ℚ)/57200000000),((15079543111:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1077710599:ℚ)/2500000000),((87063314585777577401225521760623302990246357548822741405471:ℚ)/2527418518066406250000000000000000000000000000000000000000000),((-590186584352266313793065697:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((1404761901:ℚ)/2000000000),((7125890969:ℚ)/10000000000),((2236761901:ℚ)/11535000000),((30337672907:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((979747197:ℚ)/2500000000),((47074602501981456276337930197523852189563464769392255215687067:ℚ)/1383409580581600000000000000000000000000000000000000000000000000),((-2388108274626115171556103593:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((3541679769:ℚ)/5000000000),((359270867:ℚ)/500000000),((5621679769:ℚ)/29075000000),((1525812601:ℚ)/5767500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3708462583:ℚ)/10000000000),((81535178486697802943612530945774949647290663034768887403:ℚ)/2402694108900472656250000000000000000000000000000000000000),((-316001092768637616294203:ℚ)/1945600000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/8),((3:ℚ)/16),((71429067:ℚ)/100000000),((113202207:ℚ)/156250000),((1687001:ℚ)/8750000),((479606621:ℚ)/1817187500),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3485874241:ℚ)/10000000000),((15550105019347349815538485680462269048763410083925489:ℚ)/459425745028257369995117187500000000000000000000000000),((-589625174264110020668687:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((7202451059:ℚ)/10000000000),((3652231377:ℚ)/5000000000),((11362451059:ℚ)/59100000000),((15436694131:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3248740723:ℚ)/10000000000),((3712722726064693228294598268074251490566981298664427211530171:ℚ)/109962234134609985351562500000000000000000000000000000000000000),((-607149379169218340736671577:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1815498171:ℚ)/2500000000),((1855874697:ℚ)/2500000000),((2855498171:ℚ)/15012500000),((7807624091:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1496801243:ℚ)/5000000000),((2627582078517560093853029028011376810191247344072148486795473:ℚ)/77538471050903906250000000000000000000000000000000000000000000),((-152607379087387409309153417:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((1476213599:ℚ)/2000000000),((3771262941:ℚ)/5000000000),((2308213599:ℚ)/12200000000),((15793788823:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((300760603:ℚ)/1250000000),((169909189648741207996852386033367741858216473209625398653663:ℚ)/5035918843219531250000000000000000000000000000000000000000000),((-617169969057059855864012353:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1875033283:ℚ)/2500000000),((62244439:ℚ)/80000000),((2915033283:ℚ)/15725000000),((258413317:ℚ)/976000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1622914473:ℚ)/10000000000),((19533714884065890863755096922488138347601105847768961437:ℚ)/574739134854400000000000000000000000000000000000000000000),((-8210595231758533:ℚ)/48640000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((3869117371:ℚ)/5000000000),((8018552749:ℚ)/10000000000),((5949117371:ℚ)/32400000000),((33015658247:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2756077285938625156042275610626994134881781821827410105728903:ℚ)/81637928901450000000000000000000000000000000000000000000000000),((-174463939:ℚ)/1024000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((1595260189:ℚ)/2000000000),((1984336477:ℚ)/2000000000),((2427260189:ℚ)/16000000000),((7745009431:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((85339116685139685930716952559262269129385480609285917:ℚ)/2267481600000000000000000000000000000000000000000000000),((-174463939:ℚ)/1024000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((4939929893:ℚ)/5000000000),((13725352609:ℚ)/10000000000),((2339976631:ℚ)/18400000000),((50136057827:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((24539368274632417526089452547902850350441:ℚ)/541696000000000000000000000000000000000000),((-174463939:ℚ)/1024000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC19
#check @N11Formalization.C450Source15GroupedC19.bound
#print axioms N11Formalization.C450Source15GroupedC19.valid0
#print axioms N11Formalization.C450Source15GroupedC19.valid1
#print axioms N11Formalization.C450Source15GroupedC19.valid2
#print axioms N11Formalization.C450Source15GroupedC19.valid3
#print axioms N11Formalization.C450Source15GroupedC19.valid4
#print axioms N11Formalization.C450Source15GroupedC19.valid5
#print axioms N11Formalization.C450Source15GroupedC19.valid6
#print axioms N11Formalization.C450Source15GroupedC19.valid7
#print axioms N11Formalization.C450Source15GroupedC19.valid8
#print axioms N11Formalization.C450Source15GroupedC19.valid9
#print axioms N11Formalization.C450Source15GroupedC19.valid10
#print axioms N11Formalization.C450Source15GroupedC19.valid11
#print axioms N11Formalization.C450Source15GroupedC19.valid12
#print axioms N11Formalization.C450Source15GroupedC19.valid13
#print axioms N11Formalization.C450Source15GroupedC19.bound
#print axioms N11Formalization.C450Source15GroupedC19.endpoint_checks
