import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((1134812791:ℚ)/2000000000),((6235313913:ℚ)/10000000000),((5004438373:ℚ)/10680000000),((60287197391:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7278786893:ℚ)/10000000000),((-2266454735974380906539021:ℚ)/57031200000000000000000000),((-18313890634388460325543940789:ℚ)/44359680000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((615416409:ℚ)/1000000000),((1618764257:ℚ)/2500000000),((2646249227:ℚ)/5530000000),((15491349799:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((783820029:ℚ)/1250000000),((-1152460226266342448704949375462901:ℚ)/21843500000000000000000000000000000),((-392154912534716447221291223:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((6393947453:ℚ)/10000000000),((6594870989:ℚ)/10000000000),((27181842359:ℚ)/56250000000),((62804096923:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1427740729:ℚ)/2500000000),((-923774901317542250326789118577301201:ℚ)/15820312500000000000000000000000000000),((-6358373566031404794317560367:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((6513780491:ℚ)/10000000000),((1678662287:ℚ)/2500000000),((27541341473:ℚ)/57200000000),((15910636009:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5412285737:ℚ)/10000000000),((-954958099741979077257605061438886649:ℚ)/16359200000000000000000000000000000000),((-398942025663293919997927863:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((1658394269:ℚ)/2500000000),((6834393289:ℚ)/10000000000),((6975182807:ℚ)/14537500000),((64480753023:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5098062229:ℚ)/10000000000),((-30807321719573277776354058808288593:ℚ)/528347265625000000000000000000000000),((-6407154223221047387802884167:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6753339027:ℚ)/10000000000),((6954105081:ℚ)/10000000000),((28260017081:ℚ)/59100000000),((65318735567:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((148912023:ℚ)/312500000),((-56464805221605186873071452659692589:ℚ)/970225000000000000000000000000000000),((-19291859755563671873142146741:ℚ)/44359680000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6873068041:ℚ)/10000000000),((3536893041:ℚ)/5000000000),((28619204123:ℚ)/60050000000),((33078251287:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2204697921:ℚ)/5000000000),((-1046517354905479334038267201769740887:ℚ)/18030012500000000000000000000000000000),((-4840102763135450634271623461:ℚ)/11089920000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((6992765707:ℚ)/10000000000),((3596718877:ℚ)/5000000000),((28978297121:ℚ)/61000000000),((33497032139:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((402458693:ℚ)/1000000000),((-1076249193117632221954486158856037543:ℚ)/18605000000000000000000000000000000000),((-1618926579825565485514554383:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((889054189:ℚ)/1250000000),((3716329251:ℚ)/5000000000),((3667162567:ℚ)/7862500000),((34334304757:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((72028557:ℚ)/200000000),((-481915897198469293984483738261199:ℚ)/9091015625000000000000000000000000),((-4844919647603385476355518381:ℚ)/11089920000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((7351685033:ℚ)/10000000000),((1917944327:ℚ)/2500000000),((30055055099:ℚ)/64800000000),((17585610289:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2563299037:ℚ)/10000000000),((-1104572182773476552859944088824031559:ℚ)/20995200000000000000000000000000000000),((-21458453152743987:ℚ)/48640000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((759083277:ℚ)/1000000000),((4790969269:ℚ)/5000000000),((3077249831:ℚ)/8000000000),((41856784883:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((491214221:ℚ)/10000000000),((-381271474206482420372200385188719:ℚ)/80000000000000000000000000000000000),((-2184274897809103:ℚ)/4864000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((9501175217:ℚ)/10000000000),((13393828021:ℚ)/10000000000),((36503525651:ℚ)/110400000000),((110396796147:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((278417451918101932215804451:ℚ)/6094080000000000000000000000),((-460157477:ℚ)/1024000000)⟩
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
end N11Formalization.C450Source27GroupedC23
#check @N11Formalization.C450Source27GroupedC23.bound
#print axioms N11Formalization.C450Source27GroupedC23.valid0
#print axioms N11Formalization.C450Source27GroupedC23.valid1
#print axioms N11Formalization.C450Source27GroupedC23.valid2
#print axioms N11Formalization.C450Source27GroupedC23.valid3
#print axioms N11Formalization.C450Source27GroupedC23.valid4
#print axioms N11Formalization.C450Source27GroupedC23.valid5
#print axioms N11Formalization.C450Source27GroupedC23.valid6
#print axioms N11Formalization.C450Source27GroupedC23.valid7
#print axioms N11Formalization.C450Source27GroupedC23.valid8
#print axioms N11Formalization.C450Source27GroupedC23.valid9
#print axioms N11Formalization.C450Source27GroupedC23.valid10
#print axioms N11Formalization.C450Source27GroupedC23.valid11
#print axioms N11Formalization.C450Source27GroupedC23.bound
#print axioms N11Formalization.C450Source27GroupedC23.endpoint_checks
