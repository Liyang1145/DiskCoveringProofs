import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((6176198913:ℚ)/10000000000),((1667671:ℚ)/2500000),((16:ℚ)/445),((2787671:ℚ)/24800000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((194405573:ℚ)/312500000),((381312497128737097917620334989:ℚ)/30204737408000000000000000000000),((-6053039330475867:ℚ)/243200000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((6651647713:ℚ)/10000000000),((6789509489:ℚ)/10000000000),((192:ℚ)/5435),((3756503163:ℚ)/35600000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((40393:ℚ)/80000),((4057504506649701651220438151542747619492760487820374832538171:ℚ)/333187806544400000000000000000000000000000000000000000000000000),((-6519007205955067:ℚ)/243200000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((3385250047:ℚ)/5000000000),((6908332381:ℚ)/10000000000),((96:ℚ)/2765),((11388332381:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4715719433:ℚ)/10000000000),((5571399909342531092160196431571420718949754878454090979431871:ℚ)/460277964969055078125000000000000000000000000000000000000000000),((-3317744775812773:ℚ)/121600000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((6889348953:ℚ)/10000000000),((7027152809:ℚ)/10000000000),((64:ℚ)/1875),((11507152809:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4358931849:ℚ)/10000000000),((130859274025977257312639197388219001557406870271680896839:ℚ)/10871509950000000000000000000000000000000000000000000000000),((-6751968445528227:ℚ)/243200000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((7008194469:ℚ)/10000000000),((7086562137:ℚ)/10000000000),((384:ℚ)/11345),((11566562137:ℚ)/112500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((248277307:ℚ)/625000000),((548095161797115408680555271231142356441974530891532103511321649:ℚ)/45814882434082031250000000000000000000000000000000000000000000000),((-6868444063093671:ℚ)/243200000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((3533808013:ℚ)/5000000000),((1429194179:ℚ)/2000000000),((24:ℚ)/715),((2325194179:ℚ)/22690000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3765209137:ℚ)/10000000000),((54824427883899050202142562806883207215430479004539577671:ℚ)/4593801433614250000000000000000000000000000000000000000000),((-3463340347412767:ℚ)/121600000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((7127036809:ℚ)/10000000000),((7205379097:ℚ)/10000000000),((128:ℚ)/3845),((11685379097:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3546502503:ℚ)/10000000000),((49416291228658055487893284944018117313036258070185997425845443:ℚ)/4150228741744800000000000000000000000000000000000000000000000000),((-6984916567991731:ℚ)/243200000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7186456837:ℚ)/10000000000),((1452957351:ℚ)/2000000000),((192:ℚ)/5815),((2348957351:ℚ)/23070000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3314040891:ℚ)/10000000000),((16442129845906074039597466091760102314180516928632038995101:ℚ)/1383951806726672250000000000000000000000000000000000000000000),((-7043151701213383:ℚ)/243200000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),(0:ℚ),((1:ℚ)/16),((226433629:ℚ)/312500000),((1831048471:ℚ)/2500000000),((384:ℚ)/11725),((2951048471:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3064691301:ℚ)/10000000000),((300444368321188572315942307686735807047146006972325873320469:ℚ)/25342306337978540039062500000000000000000000000000000000000000),((-221918316004111:ℚ)/7600000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7305294701:ℚ)/10000000000),((461475031:ℚ)/625000000),((32:ℚ)/985),((741475031:ℚ)/7328125000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1396965403:ℚ)/5000000000),((282338927704404297887859307618681855791621644806117796047:ℚ)/23863332060462236404418945312500000000000000000000000000000),((-7159619819367359:ℚ)/243200000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((1841178143:ℚ)/2500000000),((7502412219:ℚ)/10000000000),((192:ℚ)/6005),((11982412219:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2494792423:ℚ)/10000000000),((527876270083436220656013462162519244318215138380162962399964089:ℚ)/44662159325320650000000000000000000000000000000000000000000000000),((-1804463209650437:ℚ)/60800000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((7483546279:ℚ)/10000000000),((7621222017:ℚ)/10000000000),((48:ℚ)/1525),((12101222017:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1752834871:ℚ)/10000000000),((474451070672249896295951017578892754207259171896926524556841:ℚ)/40287350745756250000000000000000000000000000000000000000000000),((-7334316882650461:ℚ)/243200000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((60819019:ℚ)/80000000),((4048221833:ℚ)/5000000000),((4:ℚ)/135),((6288221833:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3049982892729791970385316161065039107543874013742888446361:ℚ)/258545545312500000000000000000000000000000000000000000000000),((-980059:ℚ)/32000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((201941949:ℚ)/250000000),((2499279897:ℚ)/2500000000),((3:ℚ)/125),((3619279897:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((472917773377099654914558783877371333940875136680143467:ℚ)/39858075000000000000000000000000000000000000000000000000),((-980059:ℚ)/32000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9978594547:ℚ)/10000000000),((1724739111:ℚ)/1250000000),((2:ℚ)/115),((2284739111:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((13828249151180613123632039479536329981:ℚ)/1058000000000000000000000000000000000000),((-980059:ℚ)/32000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC17
#check @N11Formalization.C450EighthGroupedC17.bound
#print axioms N11Formalization.C450EighthGroupedC17.valid0
#print axioms N11Formalization.C450EighthGroupedC17.valid1
#print axioms N11Formalization.C450EighthGroupedC17.valid2
#print axioms N11Formalization.C450EighthGroupedC17.valid3
#print axioms N11Formalization.C450EighthGroupedC17.valid4
#print axioms N11Formalization.C450EighthGroupedC17.valid5
#print axioms N11Formalization.C450EighthGroupedC17.valid6
#print axioms N11Formalization.C450EighthGroupedC17.valid7
#print axioms N11Formalization.C450EighthGroupedC17.valid8
#print axioms N11Formalization.C450EighthGroupedC17.valid9
#print axioms N11Formalization.C450EighthGroupedC17.valid10
#print axioms N11Formalization.C450EighthGroupedC17.valid11
#print axioms N11Formalization.C450EighthGroupedC17.valid12
#print axioms N11Formalization.C450EighthGroupedC17.valid13
#print axioms N11Formalization.C450EighthGroupedC17.valid14
#print axioms N11Formalization.C450EighthGroupedC17.bound
#print axioms N11Formalization.C450EighthGroupedC17.endpoint_checks
