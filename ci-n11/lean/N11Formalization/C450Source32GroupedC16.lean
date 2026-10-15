import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/16),(0:ℚ),((37967091:ℚ)/62500000),((100001737:ℚ)/156250000),((199998263:ℚ)/1609375000),((1:ℚ)/5),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1289309847:ℚ)/2000000000),((-1229912460412750208017107814335635341385769746428993:ℚ)/15631585121154785156250000000000000000000000000000000),((-627622662542637:ℚ)/3040000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6316945957:ℚ)/10000000000),((326046599:ℚ)/500000000),((633953401:ℚ)/5245000000),((496:ℚ)/2575),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1179149849:ℚ)/2000000000),((-3432901186740611459707186547541791738278543697887597:ℚ)/45090650351562500000000000000000000000000000000000000),((-105385687974992699:ℚ)/486400000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((804740001:ℚ)/1250000000),((1660419311:ℚ)/2500000000),((3139580689:ℚ)/26700000000),((992:ℚ)/5245),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((5603018427:ℚ)/10000000000),((-438347950192550186260652297413733217804700179423131597:ℚ)/5948175937500000000000000000000000000000000000000000000),((-13483252473683007:ℚ)/60800000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6558812771:ℚ)/10000000000),((1690587763:ℚ)/2500000000),((3109412237:ℚ)/27175000000),((248:ℚ)/1335),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2648074571:ℚ)/5000000000),((-1790363168207463286751696081377078345086929111538032889:ℚ)/25085263730468750000000000000000000000000000000000000000),((-110344684955502397:ℚ)/486400000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((333981433:ℚ)/500000000),((6882957203:ℚ)/10000000000),((12317042797:ℚ)/110600000000),((992:ℚ)/5435),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4972482271:ℚ)/10000000000),((-783146117275711071131527563447579073454835418751241749:ℚ)/11324489531250000000000000000000000000000000000000000000),((-5641088698669031:ℚ)/24320000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((680037177:ℚ)/1000000000),((7003499231:ℚ)/10000000000),((12196500769:ℚ)/112500000000),((496:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((289278239:ℚ)/625000000),((-1398225675555813290763412612817612748094094223068083031:ℚ)/20856857299804687500000000000000000000000000000000000000),((-11529737080291239:ℚ)/48640000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((6921045913:ℚ)/10000000000),((284959217:ℚ)/400000000),((483040783:ℚ)/4576000000),((992:ℚ)/5625),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((33274069:ℚ)/78125000),((-7787390490666685708983116620119467700600239293076531:ℚ)/119775518720000000000000000000000000000000000000000000),((-117771553601560391:ℚ)/486400000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7041654633:ℚ)/10000000000),((58918179:ℚ)/80000000),((31560607:ℚ)/315200000),((124:ℚ)/715),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3857048111:ℚ)/10000000000),((-599094952364493060051812331304545662074042933179:ℚ)/9786077440000000000000000000000000000000000000000),((-120244395031981431:ℚ)/486400000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((1820672201:ℚ)/2500000000),((190133881:ℚ)/250000000),((289866119:ℚ)/3050000000),((496:ℚ)/2955),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2899837337:ℚ)/10000000000),((-6143117267129903057866355343055708802414336308082041:ℚ)/106397343750000000000000000000000000000000000000000000),((-31296580081808407:ℚ)/121600000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((7523498187:ℚ)/10000000000),((1617193809:ℚ)/2000000000),((740935397:ℚ)/8640000000),((248:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((355016919:ℚ)/2500000000),((-13850876049092933773768213748734841372764902713180923:ℚ)/268738560000000000000000000000000000000000000000000000),((-130123636792548309:ℚ)/486400000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((4002261859:ℚ)/5000000000),((2500755553:ℚ)/2500000000),((2299244447:ℚ)/40000000000),((62:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-8085007671675994581325017390767290866987682125996462217:ℚ)/240000000000000000000000000000000000000000000000000000000),((-3465583:ℚ)/12800000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((9922822177:ℚ)/10000000000),((2764586333:ℚ)/2000000000),((1075413667:ℚ)/44160000000),((31:ℚ)/250),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1047730455802925937054930577754794940206661057323091237:ℚ)/80734371840000000000000000000000000000000000000000000000),((-3465583:ℚ)/12800000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC16
#check @N11Formalization.C450Source32GroupedC16.bound
#print axioms N11Formalization.C450Source32GroupedC16.valid0
#print axioms N11Formalization.C450Source32GroupedC16.valid1
#print axioms N11Formalization.C450Source32GroupedC16.valid2
#print axioms N11Formalization.C450Source32GroupedC16.valid3
#print axioms N11Formalization.C450Source32GroupedC16.valid4
#print axioms N11Formalization.C450Source32GroupedC16.valid5
#print axioms N11Formalization.C450Source32GroupedC16.valid6
#print axioms N11Formalization.C450Source32GroupedC16.valid7
#print axioms N11Formalization.C450Source32GroupedC16.valid8
#print axioms N11Formalization.C450Source32GroupedC16.valid9
#print axioms N11Formalization.C450Source32GroupedC16.valid10
#print axioms N11Formalization.C450Source32GroupedC16.valid11
#print axioms N11Formalization.C450Source32GroupedC16.bound
#print axioms N11Formalization.C450Source32GroupedC16.endpoint_checks
