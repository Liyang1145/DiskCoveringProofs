import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5545054653:ℚ)/10000000000),((6099671047:ℚ)/10000000000),((73795601183:ℚ)/106800000000),((21659013141:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((941301563:ℚ)/1250000000),((-16585038217414605192839746959340127027:ℚ)/152273304000000000000000000000000000000),((-2694423772099712944803439767:ℚ)/7393280000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((602183621:ℚ)/1000000000),((3169022223:ℚ)/5000000000),((7904019831:ℚ)/11060000000),((3729022223:ℚ)/4450000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6561500019:ℚ)/10000000000),((-537385944109874859552574708063072355077810996096891593:ℚ)/4227809425000000000000000000000000000000000000000000000),((-2003780466078571844219606581:ℚ)/5544960000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((3130067351:ℚ)/5000000000),((3288179761:ℚ)/5000000000),((40830740861:ℚ)/57200000000),((11544539283:ℚ)/13825000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((3014436063:ℚ)/5000000000),((-74447679299612962143874753451566988928598996592873574147:ℚ)/584841400000000000000000000000000000000000000000000000000),((-662120212698994222057122023:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3249189949:ℚ)/5000000000),((1673874247:ℚ)/2500000000),((42141089439:ℚ)/58150000000),((450894057:ℚ)/550000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((218059639:ℚ)/400000000),((-20784111679275707187131441092678004928484672112211978017:ℚ)/153616967480468750000000000000000000000000000000000000000),((-164792271167425627699430167:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((827185519:ℚ)/1250000000),((3407310969:ℚ)/5000000000),((3566346903:ℚ)/4925000000),((11901932907:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5141285753:ℚ)/10000000000),((-12614536032111006771249346600937819505735753022681609:ℚ)/93327307128906250000000000000000000000000000000000000),((-1968558201239718092607621829:ℚ)/5544960000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6736576967:ℚ)/10000000000),((693373497:ℚ)/1000000000),((86902346637:ℚ)/120100000000),((805373497:ℚ)/985000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4813046539:ℚ)/10000000000),((-730952586994184778894785101761005362765826277153298265139:ℚ)/5413511253125000000000000000000000000000000000000000000000),((-78380538583360278952978501:ℚ)/221798400000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((6855658891:ℚ)/10000000000),((1763209161:ℚ)/2500000000),((88212247801:ℚ)/122000000000),((6129627483:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4462766631:ℚ)/10000000000),((-765359036225291264227383664097182899088923141430830752303:ℚ)/5674525000000000000000000000000000000000000000000000000000),((-487593257456622211291511269:ℚ)/1386240000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6974730433:ℚ)/10000000000),((3585963743:ℚ)/5000000000),((12788862109:ℚ)/17700000000),((12437891229:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((510593583:ℚ)/1250000000),((-64849556469665638579558329000902522488451477981969203:ℚ)/481357031250000000000000000000000000000000000000000000),((-647045627861216559854887687:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((283751683:ℚ)/400000000),((7291007989:ℚ)/10000000000),((3633268513:ℚ)/5032000000),((8411007989:ℚ)/10325000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1835199267:ℚ)/5000000000),((-52323235946660410362421144096459703595035964223519:ℚ)/388840920312500000000000000000000000000000000000000),((-2575740017817856788688763023:ℚ)/7393280000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((1803211067:ℚ)/2500000000),((235285619:ℚ)/312500000),((2559480193:ℚ)/3600000000),((810856857:ℚ)/982812500),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3205620811:ℚ)/10000000000),((-2063896138707468902548647420012619540412178258934991:ℚ)/16200000000000000000000000000000000000000000000000000),((-2490695383378785273688543:ℚ)/7220000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((298036879:ℚ)/400000000),((471655537:ℚ)/500000000),((3790405669:ℚ)/6400000000),((58628393:ℚ)/60000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1983935251:ℚ)/10000000000),((-8827799424645546483969025380847369965373122657502049:ℚ)/153600000000000000000000000000000000000000000000000000),((-176097909:ℚ)/512000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9354553067:ℚ)/10000000000),((13237766319:ℚ)/10000000000),((38566694579:ℚ)/73600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-610864240372239432854472053377131919:ℚ)/49836032000000000000000000000000000000),((-176097909:ℚ)/512000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC28
#check @N11Formalization.C450Source22GroupedC28.bound
#print axioms N11Formalization.C450Source22GroupedC28.valid0
#print axioms N11Formalization.C450Source22GroupedC28.valid1
#print axioms N11Formalization.C450Source22GroupedC28.valid2
#print axioms N11Formalization.C450Source22GroupedC28.valid3
#print axioms N11Formalization.C450Source22GroupedC28.valid4
#print axioms N11Formalization.C450Source22GroupedC28.valid5
#print axioms N11Formalization.C450Source22GroupedC28.valid6
#print axioms N11Formalization.C450Source22GroupedC28.valid7
#print axioms N11Formalization.C450Source22GroupedC28.valid8
#print axioms N11Formalization.C450Source22GroupedC28.valid9
#print axioms N11Formalization.C450Source22GroupedC28.valid10
#print axioms N11Formalization.C450Source22GroupedC28.valid11
#print axioms N11Formalization.C450Source22GroupedC28.bound
#print axioms N11Formalization.C450Source22GroupedC28.endpoint_checks
