import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/8),((7:ℚ)/16),((2741596287:ℚ)/5000000000),((182035283:ℚ)/312500000),((13504788861:ℚ)/25750000000),((1954246981:ℚ)/3100000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1529739059:ℚ)/2000000000),((-6812558225705169310729136406256705762437973446204509067:ℚ)/19177956250000000000000000000000000000000000000000000000),((-1424097897759354960206709:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((5725271451:ℚ)/10000000000),((1213375709:ℚ)/2000000000),((9245271451:ℚ)/17800000000),((12845629963:ℚ)/20600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3588462999:ℚ)/5000000000),((-427276586664128884394900030785575037950401877714200202667:ℚ)/1215658787500000000000000000000000000000000000000000000000),((-14491297834384527749106759:ℚ)/36966400000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((2983507847:ℚ)/5000000000),((6187639007:ℚ)/10000000000),((14230523541:ℚ)/27175000000),((21691157683:ℚ)/35600000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6678844403:ℚ)/10000000000),((-108952108302814764826134738447008472010198296781161090050781:ℚ)/306520521200000000000000000000000000000000000000000000000000),((-363843524657452006179669711:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3043886839:ℚ)/5000000000),((6308328691:ℚ)/10000000000),((14411660517:ℚ)/27650000000),((65918300837:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1604486031:ℚ)/2500000000),((-24525871255404471046180117456760850387025228987854988001829:ℚ)/69360754214746093750000000000000000000000000000000000000000),((-362498264274655725410377959:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((6208460973:ℚ)/10000000000),((6428951299:ℚ)/10000000000),((9728460973:ℚ)/18750000000),((66762659093:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1536939591:ℚ)/2500000000),((-34863845761969789009736978327798238168883617966581434199:ℚ)/99089283398437500000000000000000000000000000000000000000),((-361073221203823049768824839:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((6329081277:ℚ)/10000000000),((1637377569:ℚ)/2500000000),((29547243831:ℚ)/57200000000),((16901642983:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5866969123:ℚ)/10000000000),((-773639668164817836228782898947122124244917177757890154401:ℚ)/2209281921386718750000000000000000000000000000000000000000),((-22473030708745552974563879:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6449638029:ℚ)/10000000000),((3335004417:ℚ)/5000000000),((29908914087:ℚ)/58150000000),((34225030919:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1393484627:ℚ)/2500000000),((-43110226107965713747966850861050000029641680919054626158087:ℚ)/123667372400000000000000000000000000000000000000000000000000),((-89496040965345957477167471:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6570134439:ℚ)/10000000000),((6790449971:ℚ)/10000000000),((10090134439:ℚ)/19700000000),((69293149797:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2633293661:ℚ)/5000000000),((-168067708688675703127230577288117161791336273793236474679689:ℚ)/484200681498437500000000000000000000000000000000000000000000),((-356320322005547637607776999:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((6690573499:ℚ)/10000000000),((109862047:ℚ)/156250000),((30631720497:ℚ)/61000000000),((1109034329:ℚ)/1846875000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((98844147:ℚ)/200000000),((-271962467629107225149259908003041316853969121331730287:ℚ)/800573306465148925781250000000000000000000000000000000),((-143889912976489740775503:ℚ)/380000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((1386258117:ℚ)/2000000000),((7512035971:ℚ)/10000000000),((2090258117:ℚ)/4320000000),((74344251797:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((4226335467:ℚ)/10000000000),((-100097067749425104900238725263500931920045232082200087961799:ℚ)/306424350000000000000000000000000000000000000000000000000000),((-336239457359133811558644999:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((3706074183:ℚ)/5000000000),((2357462217:ℚ)/2500000000),((16398222549:ℚ)/40000000000),((21942235519:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((556998891:ℚ)/2500000000),((-19264760454358964409162723959830832776303902287192930917:ℚ)/70858800000000000000000000000000000000000000000000000000),((-7238024713433763:ℚ)/19456000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((1166242443:ℚ)/1250000000),((662532011:ℚ)/500000000),((1606242443:ℚ)/4600000000),((5725724077:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-4231660731978662446844395021187475433722696654620515931:ℚ)/18400000000000000000000000000000000000000000000000000000),((-48226791:ℚ)/128000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC23
#check @N11Formalization.C450Source35GroupedC23.bound
#print axioms N11Formalization.C450Source35GroupedC23.valid0
#print axioms N11Formalization.C450Source35GroupedC23.valid1
#print axioms N11Formalization.C450Source35GroupedC23.valid2
#print axioms N11Formalization.C450Source35GroupedC23.valid3
#print axioms N11Formalization.C450Source35GroupedC23.valid4
#print axioms N11Formalization.C450Source35GroupedC23.valid5
#print axioms N11Formalization.C450Source35GroupedC23.valid6
#print axioms N11Formalization.C450Source35GroupedC23.valid7
#print axioms N11Formalization.C450Source35GroupedC23.valid8
#print axioms N11Formalization.C450Source35GroupedC23.valid9
#print axioms N11Formalization.C450Source35GroupedC23.valid10
#print axioms N11Formalization.C450Source35GroupedC23.valid11
#print axioms N11Formalization.C450Source35GroupedC23.bound
#print axioms N11Formalization.C450Source35GroupedC23.endpoint_checks
