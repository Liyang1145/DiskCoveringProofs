import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((6248183023:ℚ)/10000000000),((3266766763:ℚ)/5000000000),((-4360300289:ℚ)/49600000000),((-4739641:ℚ)/500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6056550651:ℚ)/10000000000),((5581906711560599300826048704267805097361855260117759:ℚ)/72656250000000000000000000000000000000000000000000000),((-60778908765176607053996331:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((3243524493:ℚ)/5000000000),((105819187:ℚ)/156250000),((-147457561:ℚ)/1609375000),((-121174831:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5480174933:ℚ)/10000000000),((8620442364254092049189979176026869500925644004698485339:ℚ)/113455948437500000000000000000000000000000000000000000000),((-50216353656393323652413833:ℚ)/693120000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((1345163393:ℚ)/2000000000),((6891838321:ℚ)/10000000000),((-9795514963:ℚ)/106800000000),((-193163393:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4843540403:ℚ)/10000000000),((53483682102511874214631645787825509141873741352159416339:ℚ)/714428311043750000000000000000000000000000000000000000000),((-2925618689389032017675211:ℚ)/36966400000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((213911483:ℚ)/312500000),((3505612901:ℚ)/5000000000),((-5076838703:ℚ)/54350000000),((-33911483:ℚ)/1728125000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2247322143:ℚ)/5000000000),((122526503368709740718033710092993324043857145521951269:ℚ)/1643524948945641517639160156250000000000000000000000000),((-74449827978410675988971:ℚ)/902500000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6964497163:ℚ)/10000000000),((7130591583:ℚ)/10000000000),((-1501682107:ℚ)/15800000000),((-1204497163:ℚ)/56250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4118515513:ℚ)/10000000000),((76480038786715520195684143063017759259094890395917032837:ℚ)/1029807329177856445312500000000000000000000000000000000000),((-79335146580902716985979891:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((141676143:ℚ)/200000000),((1812484189:ℚ)/2500000000),((-2717452567:ℚ)/28125000000),((-26476143:ℚ)/1144000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((115838659:ℚ)/312500000),((2077537442195018829812104816731826142171190197252903:ℚ)/28072387200000000000000000000000000000000000000000000),((-98923273891874488453633:ℚ)/1108992000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7203098409:ℚ)/10000000000),((368463117:ℚ)/500000000),((-561389351:ℚ)/5720000000),((-1443098409:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((50719861:ℚ)/156250000),((1178557348580387631629680492498143142582491146876648673519:ℚ)/15976164617968750000000000000000000000000000000000000000000),((-256618179646736796023617777:ℚ)/2772480000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3661185933:ℚ)/5000000000),((7488569289:ℚ)/10000000000),((-11585707867:ℚ)/116300000000),((-260395311:ℚ)/9850000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2711258639:ℚ)/10000000000),((127737782602869242120956290750602376557104854017515260999:ℚ)/1736634531054687500000000000000000000000000000000000000000),((-66483873190552588930002313:ℚ)/693120000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((3720814193:ℚ)/5000000000),((7727130797:ℚ)/10000000000),((-12301392391:ℚ)/118200000000),((-840814193:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2045050031:ℚ)/10000000000),((7727564937303202656717318237898964275483011409748963379781:ℚ)/104801383593750000000000000000000000000000000000000000000000),((-22938348986968283762098411:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7680093809:ℚ)/10000000000),((4102032967:ℚ)/5000000000),((-6866098901:ℚ)/61000000000),((-1920093809:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((42013449714365726674957104104542388475614777565769171769:ℚ)/566870400000000000000000000000000000000000000000000000000),((-1660069:ℚ)/16000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((4078426937:ℚ)/5000000000),((5054979951:ℚ)/5000000000),((-9724939853:ℚ)/64800000000),((-1198426937:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((837214588634976845785456390071282834324768106561205150713:ℚ)/10800000000000000000000000000000000000000000000000000000000),((-1660069:ℚ)/16000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((1006221529:ℚ)/1000000000),((2783373161:ℚ)/2000000000),((-6174119483:ℚ)/32000000000),((-430221529:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((541957646298869729231215931193072419728218841540750921:ℚ)/6307372800000000000000000000000000000000000000000000000),((-1660069:ℚ)/16000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC14
#check @N11Formalization.C450Source19GroupedC14.bound
#print axioms N11Formalization.C450Source19GroupedC14.valid0
#print axioms N11Formalization.C450Source19GroupedC14.valid1
#print axioms N11Formalization.C450Source19GroupedC14.valid2
#print axioms N11Formalization.C450Source19GroupedC14.valid3
#print axioms N11Formalization.C450Source19GroupedC14.valid4
#print axioms N11Formalization.C450Source19GroupedC14.valid5
#print axioms N11Formalization.C450Source19GroupedC14.valid6
#print axioms N11Formalization.C450Source19GroupedC14.valid7
#print axioms N11Formalization.C450Source19GroupedC14.valid8
#print axioms N11Formalization.C450Source19GroupedC14.valid9
#print axioms N11Formalization.C450Source19GroupedC14.valid10
#print axioms N11Formalization.C450Source19GroupedC14.valid11
#print axioms N11Formalization.C450Source19GroupedC14.bound
#print axioms N11Formalization.C450Source19GroupedC14.endpoint_checks
