import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/16),((1:ℚ)/4),((2859273839:ℚ)/5000000000),((3029036963:ℚ)/5000000000),((19137821517:ℚ)/51500000000),((5749036963:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((89879603:ℚ)/125000000),((-239314406914112017552876535810835855970077609730617657355797:ℚ)/820398942968750000000000000000000000000000000000000000000000),((-1138211026512726287470101:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((2980690647:ℚ)/5000000000),((3089631021:ℚ)/5000000000),((19502071941:ℚ)/52450000000),((5809631021:ℚ)/12875000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((3345402949:ℚ)/5000000000),((-695901112287588493841759328281639070786336957098844143672709:ℚ)/2391833547898632812500000000000000000000000000000000000000000),((-60967752150325222190231:ℚ)/190000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((6082648521:ℚ)/10000000000),((6300360817:ℚ)/10000000000),((147445489:ℚ)/400000000),((11740360817:ℚ)/26225000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((6429200679:ℚ)/10000000000),((-31654765928868884270313563200203975159883489144452932881:ℚ)/110040100000000000000000000000000000000000000000000000000),((-4650445939225349178151581:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((6203823421:ℚ)/10000000000),((3210687559:ℚ)/5000000000),((39731470263:ℚ)/108700000000),((1976895853:ℚ)/4450000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6158330033:ℚ)/10000000000),((-18093280255583656867196616821013146700182320312228655741077263:ℚ)/63584119682893750000000000000000000000000000000000000000000000),((-1166609269623080307528549:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6324911029:ℚ)/10000000000),((3271154731:ℚ)/5000000000),((40094733087:ℚ)/110600000000),((5991154731:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((58768733:ℚ)/100000000),((-43961679802888555532357396319284403484856075410034543805854367:ℚ)/156107767327744531250000000000000000000000000000000000000000000),((-1170381314069682457389069:ℚ)/3610000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((6445916019:ℚ)/10000000000),((3331584023:ℚ)/5000000000),((13485916019:ℚ)/37500000000),((6051584023:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5583189869:ℚ)/10000000000),((-66170019790885609907787847162670597136822434364061874321:ℚ)/237321853637695312500000000000000000000000000000000000000),((-1173928239070769116014741:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((1641710683:ℚ)/2500000000),((6783954777:ℚ)/10000000000),((10205132049:ℚ)/28600000000),((12223954777:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2637598853:ℚ)/5000000000),((-1090245397280453249138378851414623403011832465702830701627:ℚ)/3947679450000000000000000000000000000000000000000000000000),((-4709002484938465262710541:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((668769521:ℚ)/1000000000),((1380934659:ℚ)/2000000000),((4118308563:ℚ)/11630000000),((2468934659:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((247509277:ℚ)/500000000),((-55018703302257071685519263871684759582937538086417804475163:ℚ)/201044055552518750000000000000000000000000000000000000000000),((-188855839607706903999749:ℚ)/577600000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6808477217:ℚ)/10000000000),((3512663499:ℚ)/5000000000),((13848477217:ℚ)/39400000000),((6232663499:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4604508211:ℚ)/10000000000),((-35066708717834299480804550355083581103695316541918579467398993:ℚ)/129261181415462500000000000000000000000000000000000000000000000),((-1183223867916002838411629:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((6929192267:ℚ)/10000000000),((7266452441:ℚ)/10000000000),((41907576801:ℚ)/122000000000),((4235484147:ℚ)/9850000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4233061761:ℚ)/10000000000),((-116571592224908567231209107437938125180242344217541864152800881:ℚ)/440445281450000000000000000000000000000000000000000000000000000),((-4690743149618229495573549:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((3585217203:ℚ)/5000000000),((3874026141:ℚ)/5000000000),((7105217203:ℚ)/21600000000),((6594026141:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3378236671:ℚ)/10000000000),((-2196849728383799525894258813013616543153455363947292244849:ℚ)/8680348800000000000000000000000000000000000000000000000000),((-392847591925239:ℚ)/1216000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((47826539:ℚ)/62500000),((9668086533:ℚ)/10000000000),((275479617:ℚ)/1000000000),((15108086533:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-977000559249527049904078655512821145278547013992590953:ℚ)/4556250000000000000000000000000000000000000000000000000),((-5415519:ℚ)/16000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9572920859:ℚ)/10000000000),((539658159:ℚ)/400000000),((16612920859:ℚ)/73600000000),((757258159:ℚ)/1600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-112468882876841621362979730964788866084272263557622023611:ℚ)/622950400000000000000000000000000000000000000000000000000),((-5415519:ℚ)/16000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC20
#check @N11Formalization.C450Source35GroupedC20.bound
#print axioms N11Formalization.C450Source35GroupedC20.valid0
#print axioms N11Formalization.C450Source35GroupedC20.valid1
#print axioms N11Formalization.C450Source35GroupedC20.valid2
#print axioms N11Formalization.C450Source35GroupedC20.valid3
#print axioms N11Formalization.C450Source35GroupedC20.valid4
#print axioms N11Formalization.C450Source35GroupedC20.valid5
#print axioms N11Formalization.C450Source35GroupedC20.valid6
#print axioms N11Formalization.C450Source35GroupedC20.valid7
#print axioms N11Formalization.C450Source35GroupedC20.valid8
#print axioms N11Formalization.C450Source35GroupedC20.valid9
#print axioms N11Formalization.C450Source35GroupedC20.valid10
#print axioms N11Formalization.C450Source35GroupedC20.valid11
#print axioms N11Formalization.C450Source35GroupedC20.valid12
#print axioms N11Formalization.C450Source35GroupedC20.bound
#print axioms N11Formalization.C450Source35GroupedC20.endpoint_checks
