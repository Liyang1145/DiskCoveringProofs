import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/16),((1:ℚ)/4),((5754866251:ℚ)/10000000000),((6088723183:ℚ)/10000000000),((37104598753:ℚ)/103000000000),((11208723183:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7117511679:ℚ)/10000000000),((-479512301367753272614763971464455545814612162870090828843923:ℚ)/1968957463125000000000000000000000000000000000000000000000000),((-73470372977542614870317419:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((5997072599:ℚ)/10000000000),((6330432369:ℚ)/10000000000),((37831217797:ℚ)/106800000000),((11450432369:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1322945199:ℚ)/2000000000),((-480472595582824086316457905051305547385466926299206089853901:ℚ)/2019334352670000000000000000000000000000000000000000000000000),((-3901815598336653443178249:ℚ)/12160000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((6238934743:ℚ)/10000000000),((6451173791:ℚ)/10000000000),((38556804229:ℚ)/108700000000),((11571173791:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3038946377:ℚ)/5000000000),((-4528798740275445616542792865612369166846059699426931137718351:ℚ)/19075235904868125000000000000000000000000000000000000000000000),((-75473380678178582318968651:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3179874213:ℚ)/5000000000),((3285922561:ℚ)/5000000000),((19459622639:ℚ)/55300000000),((5845922561:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5793676907:ℚ)/10000000000),((-196468694719567671127752664978634727081469644851425296106523:ℚ)/836291610684345703125000000000000000000000000000000000000000),((-18942545501020922839060491:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((648048941:ℚ)/1000000000),((267698001:ℚ)/400000000),((3928146823:ℚ)/11250000000),((472498001:ℚ)/1106000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((687089863:ℚ)/1250000000),((-9388311602477069068108074579372296589249543618572934043:ℚ)/40368447303771972656250000000000000000000000000000000000),((-121685195232635199451371:ℚ)/369664000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((6601161501:ℚ)/10000000000),((851623989:ℚ)/1250000000),((39643484503:ℚ)/114400000000),((1491623989:ℚ)/3515625000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2592395491:ℚ)/5000000000),((-5819113175650962987916740900231774668468366354883746499197:ℚ)/25265148480000000000000000000000000000000000000000000000000),((-1192540762697837895316891:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((6721768241:ℚ)/10000000000),((1733368491:ℚ)/2500000000),((40005304723:ℚ)/116300000000),((3013368491:ℚ)/7150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4854968817:ℚ)/10000000000),((-4587627078109838129735536256659181014351167283166129853848651:ℚ)/20104405555251875000000000000000000000000000000000000000000000),((-4786143635648904359772051:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6842312931:ℚ)/10000000000),((7053899147:ℚ)/10000000000),((40366938793:ℚ)/118200000000),((12173899147:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2251640601:ℚ)/5000000000),((-8770285363311035181832712764629743541850162118450890961044721:ℚ)/38778354424638750000000000000000000000000000000000000000000000),((-76820343808853705220357939:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((6962798653:ℚ)/10000000000),((7294589829:ℚ)/10000000000),((40728395959:ℚ)/122000000000),((12414589829:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4124094873:ℚ)/10000000000),((-29146428679198972822907680602622680562519225924122091494227029:ℚ)/132133584435000000000000000000000000000000000000000000000000000),((-76239905767641184045403411:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7203604519:ℚ)/10000000000),((3887699809:ℚ)/5000000000),((41450813557:ℚ)/129600000000),((6447699809:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((405497809:ℚ)/1250000000),((-355661637443493935046813948252152713615661973602382285519583:ℚ)/1687459806720000000000000000000000000000000000000000000000000),((-4009120029359929:ℚ)/12160000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7684623661:ℚ)/10000000000),((4846522821:ℚ)/5000000000),((42893870983:ℚ)/160000000000),((7406522821:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-332127998561710200411128943540364228077494133580813620437279:ℚ)/1866240000000000000000000000000000000000000000000000000000000),((-1101701:ℚ)/3200000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9602902799:ℚ)/10000000000),((540545733:ℚ)/400000000),((48648708397:ℚ)/220800000000),((745345733:ℚ)/1600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-750219347315044386320722443004827732202872077006067877447:ℚ)/5045898240000000000000000000000000000000000000000000000000),((-1101701:ℚ)/3200000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC20
#check @N11Formalization.C450Source33GroupedC20.bound
#print axioms N11Formalization.C450Source33GroupedC20.valid0
#print axioms N11Formalization.C450Source33GroupedC20.valid1
#print axioms N11Formalization.C450Source33GroupedC20.valid2
#print axioms N11Formalization.C450Source33GroupedC20.valid3
#print axioms N11Formalization.C450Source33GroupedC20.valid4
#print axioms N11Formalization.C450Source33GroupedC20.valid5
#print axioms N11Formalization.C450Source33GroupedC20.valid6
#print axioms N11Formalization.C450Source33GroupedC20.valid7
#print axioms N11Formalization.C450Source33GroupedC20.valid8
#print axioms N11Formalization.C450Source33GroupedC20.valid9
#print axioms N11Formalization.C450Source33GroupedC20.valid10
#print axioms N11Formalization.C450Source33GroupedC20.valid11
#print axioms N11Formalization.C450Source33GroupedC20.bound
#print axioms N11Formalization.C450Source33GroupedC20.endpoint_checks
