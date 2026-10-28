import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6028216351:ℚ)/10000000000),((3284821627:ℚ)/5000000000),((19468216351:ℚ)/106800000000),((6804821627:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3273863563:ℚ)/5000000000),((2698515679189984336657763527274300985589:ℚ)/22653553056000000000000000000000000000000),((-16963048477273597914452423:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6507652527:ℚ)/10000000000),((6808973059:ℚ)/10000000000),((19947652527:ℚ)/110600000000),((4616324353:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((169622381:ℚ)/312500000),((304484727324937601351969748782823820729740124411498251963919:ℚ)/2694823311512500000000000000000000000000000000000000000000000),((-72474663904619949080026647:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6747139069:ℚ)/10000000000),((6928591093:ℚ)/10000000000),((20187139069:ℚ)/112500000000),((13968591093:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4782939361:ℚ)/10000000000),((37565283912922949866735549066883925084851038689478829093:ℚ)/339734685937500000000000000000000000000000000000000000000),((-74779655990420165522442663:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((686683141:ℚ)/1000000000),((1762044997:ℚ)/2500000000),((2030683141:ℚ)/11440000000),((391338333:ℚ)/1562500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2214292173:ℚ)/5000000000),((1032661348825391503176596467178163552269994048448433167:ℚ)/9375810623168945312500000000000000000000000000000000000),((-4740869716643763313186983:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6986492089:ℚ)/10000000000),((716774119:ℚ)/1000000000),((20426492089:ℚ)/116300000000),((1420774119:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((809122041:ℚ)/2000000000),((986706938113225196692827971108986199463255834745856239283:ℚ)/8989072131325000000000000000000000000000000000000000000000),((-769252710006598515405807:ℚ)/2310400000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((177653067:ℚ)/250000000),((1457455211:ℚ)/2000000000),((171217689:ℚ)/985000000),((2865455211:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3624917439:ℚ)/10000000000),((2610000023031694680275111688288136175652650995645337777253:ℚ)/23846883563798046875000000000000000000000000000000000000000),((-164197344715507291469533:ℚ)/486400000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((1445144931:ℚ)/2000000000),((7526271753:ℚ)/10000000000),((4133144931:ℚ)/24400000000),((14566271753:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((393923997:ℚ)/1250000000),((132403753354287376345442773565699667716733161820761838471191:ℚ)/1200168264360937500000000000000000000000000000000000000000000),((-236688501059192786685603949:ℚ)/693120000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7464848181:ℚ)/10000000000),((1000499721:ℚ)/1250000000),((2322760909:ℚ)/14400000000),((1880499721:ℚ)/7625000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((944354069:ℚ)/5000000000),((174457344332150491111124932795438098288858135669131927:ℚ)/1558554840087890625000000000000000000000000000000000000),((-42760907116224271:ℚ)/121600000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((3971403481:ℚ)/5000000000),((1239036981:ℚ)/1250000000),((10691403481:ℚ)/80000000000),((2119036981:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6269590290845713531444625529607376605680399623883307:ℚ)/51898535156250000000000000000000000000000000000000000),((-5722391:ℚ)/16000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((4925906041:ℚ)/5000000000),((1372201111:ℚ)/1000000000),((11645906041:ℚ)/110400000000),((2076201111:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((7351537027242217720065967537818419377:ℚ)/50784000000000000000000000000000000000),((-5722391:ℚ)/16000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC18
#check @N11Formalization.C450Source23GroupedC18.bound
#print axioms N11Formalization.C450Source23GroupedC18.valid0
#print axioms N11Formalization.C450Source23GroupedC18.valid1
#print axioms N11Formalization.C450Source23GroupedC18.valid2
#print axioms N11Formalization.C450Source23GroupedC18.valid3
#print axioms N11Formalization.C450Source23GroupedC18.valid4
#print axioms N11Formalization.C450Source23GroupedC18.valid5
#print axioms N11Formalization.C450Source23GroupedC18.valid6
#print axioms N11Formalization.C450Source23GroupedC18.valid7
#print axioms N11Formalization.C450Source23GroupedC18.valid8
#print axioms N11Formalization.C450Source23GroupedC18.valid9
#print axioms N11Formalization.C450Source23GroupedC18.bound
#print axioms N11Formalization.C450Source23GroupedC18.endpoint_checks
