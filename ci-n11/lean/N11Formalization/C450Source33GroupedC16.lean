import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/16),(0:ℚ),((6066432227:ℚ)/10000000000),((6394921351:ℚ)/10000000000),((13445078649:ℚ)/103000000000),((32:ℚ)/155),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1292941247:ℚ)/2000000000),((-65084734201856133460601209460935540121236077325783357013817:ℚ)/656319154375000000000000000000000000000000000000000000000000),((-39397486091379877:ℚ)/194560000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6308962373:ℚ)/10000000000),((6515886471:ℚ)/10000000000),((13324113529:ℚ)/104900000000),((512:ℚ)/2575),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5914615761:ℚ)/10000000000),((-184251406065993079035810187248807586786027988389996150821217:ℚ)/1913466838318906250000000000000000000000000000000000000000000),((-41366091402484723:ℚ)/194560000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((6430086627:ℚ)/10000000000),((1659192659:ℚ)/2500000000),((3300807341:ℚ)/26700000000),((1024:ℚ)/5245),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((5622383109:ℚ)/10000000000),((-306102281919104030031218378165941192068458265832746344461253:ℚ)/3272689374900468750000000000000000000000000000000000000000000),((-42349251037114277:ℚ)/194560000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6551123947:ℚ)/10000000000),((1689394561:ℚ)/2500000000),((3270605439:ℚ)/27175000000),((256:ℚ)/1335),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5316140461:ℚ)/10000000000),((-27094767738427690862633402305279535305456898704250827511621:ℚ)/298050561013564453125000000000000000000000000000000000000000),((-43331705032725597:ℚ)/194560000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((6672079063:ℚ)/10000000000),((6878313373:ℚ)/10000000000),((12961686627:ℚ)/110600000000),((1024:ℚ)/5435),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2496633713:ℚ)/5000000000),((-197154053945583497599496768829120635156814870090294048051837:ℚ)/2230110961824921875000000000000000000000000000000000000000000),((-44313491782496913:ℚ)/194560000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((424559773:ℚ)/625000000),((874872477:ℚ)/1250000000),((1605127523:ℚ)/14062500000),((512:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2325128417:ℚ)/5000000000),((-6782253342965691279114704500936966252004985335589660143:ℚ)/78844623640179634094238281250000000000000000000000000000),((-2830915434012123:ℚ)/12160000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((6913759941:ℚ)/10000000000),((1423916221:ℚ)/2000000000),((2544083779:ℚ)/22880000000),((1024:ℚ)/5625),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((856445221:ℚ)/2000000000),((-16926410986912712824293180002072426409839038517963426329:ℚ)/202121187840000000000000000000000000000000000000000000000),((-46275203626859891:ℚ)/194560000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7034493583:ℚ)/10000000000),((3680300581:ℚ)/5000000000),((6239699419:ℚ)/59100000000),((128:ℚ)/715),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3882016893:ℚ)/10000000000),((-5823884236225391368643597835469131566937941562149088812867:ℚ)/73284483973593750000000000000000000000000000000000000000000),((-47255192683025433:ℚ)/194560000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((28420957:ℚ)/39062500),((7601397347:ℚ)/10000000000),((12238602653:ℚ)/122000000000),((512:ℚ)/2955),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((366441283:ℚ)/1250000000),((-9985470549438364333848946512085793747493329203617320907434927:ℚ)/132133584435000000000000000000000000000000000000000000000000000),((-192240550342107:ℚ)/760000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((751679619:ℚ)/1000000000),((8082398893:ℚ)/10000000000),((1306400123:ℚ)/14400000000),((256:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1481074223:ℚ)/10000000000),((-158902028649517595809574456307024206319748399982178149777:ℚ)/2314759680000000000000000000000000000000000000000000000000),((-5117001931121669:ℚ)/19456000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((7998224801:ℚ)/10000000000),((400024993:ℚ)/400000000),((393575007:ℚ)/6400000000),((64:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-5846230770786688297328009338306467526707487161852181031:ℚ)/119439360000000000000000000000000000000000000000000000000),((-34108803:ℚ)/128000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((2479435419:ℚ)/2500000000),((13821895451:ℚ)/10000000000),((6018104549:ℚ)/220800000000),((16:ℚ)/125),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-133755002065676236848442524094878669209349063848085587711:ℚ)/5045898240000000000000000000000000000000000000000000000000),((-34108803:ℚ)/128000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC16
#check @N11Formalization.C450Source33GroupedC16.bound
#print axioms N11Formalization.C450Source33GroupedC16.valid0
#print axioms N11Formalization.C450Source33GroupedC16.valid1
#print axioms N11Formalization.C450Source33GroupedC16.valid2
#print axioms N11Formalization.C450Source33GroupedC16.valid3
#print axioms N11Formalization.C450Source33GroupedC16.valid4
#print axioms N11Formalization.C450Source33GroupedC16.valid5
#print axioms N11Formalization.C450Source33GroupedC16.valid6
#print axioms N11Formalization.C450Source33GroupedC16.valid7
#print axioms N11Formalization.C450Source33GroupedC16.valid8
#print axioms N11Formalization.C450Source33GroupedC16.valid9
#print axioms N11Formalization.C450Source33GroupedC16.valid10
#print axioms N11Formalization.C450Source33GroupedC16.valid11
#print axioms N11Formalization.C450Source33GroupedC16.bound
#print axioms N11Formalization.C450Source33GroupedC16.endpoint_checks
