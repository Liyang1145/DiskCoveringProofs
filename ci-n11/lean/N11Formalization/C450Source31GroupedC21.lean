import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/4),((5:ℚ)/16),((5719310869:ℚ)/10000000000),((1512190551:ℚ)/2500000000),((10359310869:ℚ)/25750000000),((2472190551:ℚ)/4960000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((14377687:ℚ)/20000000),((-23084512624969634393926292799208389980056343553736064943:ℚ)/106711621093750000000000000000000000000000000000000000000),((-63680151542861638963072747:ℚ)/184832000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((1490193481:ℚ)/2500000000),((786228391:ℚ)/1250000000),((883397827:ℚ)/2225000000),((1266228391:ℚ)/2575000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1673023557:ℚ)/2500000000),((-3650256918912137510395595356452428182199600666822521:ℚ)/17211157226562500000000000000000000000000000000000000),((-16002498943545884032720907:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3100974189:ℚ)/5000000000),((3205132053:ℚ)/5000000000),((5420974189:ℚ)/13587500000),((1708377351:ℚ)/3560000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((308129993:ℚ)/500000000),((-3333016118775672348444783496557396577091569432253955103:ℚ)/15678289831542968750000000000000000000000000000000000000),((-259756245265298672409647523:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1580609281:ℚ)/2500000000),((3265320963:ℚ)/5000000000),((2740609281:ℚ)/6912500000),((5185320963:ℚ)/10870000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5882741777:ℚ)/10000000000),((-970773171681565963524896086412094269497613751223389:ℚ)/4607946586608886718750000000000000000000000000000000),((-260292148132795209708877843:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((3221432429:ℚ)/5000000000),((1330192733:ℚ)/2000000000),((1847144143:ℚ)/4687500000),((299741819:ℚ)/632000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5590763571:ℚ)/10000000000),((-58352477080644576885085542199235440462829008520381:ℚ)/279396772384643554687500000000000000000000000000000),((-41724716739600052139808083:ℚ)/118292480000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((1640808689:ℚ)/2500000000),((677123219:ℚ)/1000000000),((2800808689:ℚ)/7150000000),((1061123219:ℚ)/2250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2642310393:ℚ)/5000000000),((-473165264157507839416137292714912054986580666033453003:ℚ)/2284536718750000000000000000000000000000000000000000000),((-10448732998242331922735667:ℚ)/29573120000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3341774889:ℚ)/5000000000),((3445725087:ℚ)/5000000000),((5661774889:ℚ)/14537500000),((5365725087:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((496165539:ℚ)/1000000000),((-3945331996586363550702099674011665345151140948543959587:ℚ)/19202120935058593750000000000000000000000000000000000000),((-261608763577000309116357243:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3401906341:ℚ)/5000000000),((3505810057:ℚ)/5000000000),((5721906341:ℚ)/14775000000),((5425810057:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4618301389:ℚ)/10000000000),((-114169686133773221212324831675621889475871401935356943:ℚ)/559963842773437500000000000000000000000000000000000000),((-261950869487070759233164203:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((3462013023:ℚ)/5000000000),((7251825047:ℚ)/10000000000),((5782013023:ℚ)/15250000000),((11091825047:ℚ)/23640000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4249579783:ℚ)/10000000000),((-4406320102809434703049996334736037684347085827486199789:ℚ)/22166113281250000000000000000000000000000000000000000000),((-1037481894233374433038745323:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7164313627:ℚ)/10000000000),((3865875841:ℚ)/5000000000),((145732267:ℚ)/400000000),((5785875841:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3402452617:ℚ)/10000000000),((-75895023261187786333361457495039036694075166301961:ℚ)/400000000000000000000000000000000000000000000000000),((-338163008594406689:ℚ)/972800000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((47777441:ℚ)/62500000),((1929344963:ℚ)/2000000000),((76777441:ℚ)/250000000),((2697344963:ℚ)/5184000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-15384916249649452895510389068796971751966814609947:ℚ)/97656250000000000000000000000000000000000000000000),((-371628301:ℚ)/1024000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((4779909409:ℚ)/5000000000),((13464217537:ℚ)/10000000000),((7099909409:ℚ)/27600000000),((17304217537:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-156481032984217169475853624740256033764302104746353209:ℚ)/1216700000000000000000000000000000000000000000000000000),((-371628301:ℚ)/1024000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC21
#check @N11Formalization.C450Source31GroupedC21.bound
#print axioms N11Formalization.C450Source31GroupedC21.valid0
#print axioms N11Formalization.C450Source31GroupedC21.valid1
#print axioms N11Formalization.C450Source31GroupedC21.valid2
#print axioms N11Formalization.C450Source31GroupedC21.valid3
#print axioms N11Formalization.C450Source31GroupedC21.valid4
#print axioms N11Formalization.C450Source31GroupedC21.valid5
#print axioms N11Formalization.C450Source31GroupedC21.valid6
#print axioms N11Formalization.C450Source31GroupedC21.valid7
#print axioms N11Formalization.C450Source31GroupedC21.valid8
#print axioms N11Formalization.C450Source31GroupedC21.valid9
#print axioms N11Formalization.C450Source31GroupedC21.valid10
#print axioms N11Formalization.C450Source31GroupedC21.valid11
#print axioms N11Formalization.C450Source31GroupedC21.bound
#print axioms N11Formalization.C450Source31GroupedC21.endpoint_checks
