import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((3138212179:ℚ)/5000000000),((6554624407:ℚ)/10000000000),((-4474624407:ℚ)/24800000000),((-4934636537:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5990967169:ℚ)/10000000000),((1372306436254067427652672417335843897992335774090352302057:ℚ)/26464482031250000000000000000000000000000000000000000000000),((38213400457096566054689633:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((1628676103:ℚ)/2500000000),((6792941081:ℚ)/10000000000),((-4712941081:ℚ)/25750000000),((-2646028309:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5409925587:ℚ)/10000000000),((52492298784327198352449183984690088087553652042203962951:ℚ)/1021103535937500000000000000000000000000000000000000000000),((6212019126889253899955817:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6752928703:ℚ)/10000000000),((6912077901:ℚ)/10000000000),((-4832077901:ℚ)/26700000000),((-11298786109:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2383180827:ℚ)/5000000000),((108313811098177189832965314059946850542383915368728324999217:ℚ)/2143284933131250000000000000000000000000000000000000000000000),((45895971481963588677058617:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((274880871:ℚ)/400000000),((7031201367:ℚ)/10000000000),((-4951201367:ℚ)/27175000000),((-466242613:ℚ)/4424000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4412620373:ℚ)/10000000000),((463031765237807787903256268126783291660809006676082029:ℚ)/9191257689950000000000000000000000000000000000000000000),((30614819330015883627433:ℚ)/23658496000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((699110301:ℚ)/1000000000),((1772689577:ℚ)/2500000000),((-1252689577:ℚ)/6912500000),((-1201330903:ℚ)/11155000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((503771103:ℚ)/1250000000),((14990334592909504539088908283325939005662718538032673801:ℚ)/299842983018701171875000000000000000000000000000000000000),((-211542047310099652967:ℚ)/409600000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((352531969:ℚ)/500000000),((7150312161:ℚ)/10000000000),((-5070312161:ℚ)/27887500000),((-609595907:ℚ)/5625000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3825501669:ℚ)/10000000000),((161335896334198802184096831645387948863306310773681729:ℚ)/3231364488601684570312500000000000000000000000000000000),((-52564081396469833742407:ℚ)/36966400000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1777543253:ℚ)/2500000000),((3604931503:ℚ)/5000000000),((-2564931503:ℚ)/14062500000),((-3092629759:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((360985847:ℚ)/1000000000),((159990085192034958894154808844031209548444787355220681:ℚ)/3208455809967041015625000000000000000000000000000000000),((-2151059426239855123883983:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((3584851989:ℚ)/5000000000),((3634705459:ℚ)/5000000000),((-2594705459:ℚ)/14181250000),((-6274555967:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1690567631:ℚ)/5000000000),((132182879543380578896013034019207133929225387816142404317293:ℚ)/2654010273200000000000000000000000000000000000000000000000000),((-11952659620704263104757327:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((7229232343:ℚ)/10000000000),((7328955969:ℚ)/10000000000),((-5248955969:ℚ)/28600000000),((-12727697029:ℚ)/115350000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((784116757:ℚ)/2500000000),((888543800344830302936807419980166407028937214668837719:ℚ)/17861076531463623046875000000000000000000000000000000000),((-61206709777649034251460663:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((7288758173:ℚ)/10000000000),((7388498231:ℚ)/10000000000),((-5308498231:ℚ)/28837500000),((-12906274519:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2871776049:ℚ)/10000000000),((1127090877423052008455696892066756733768445710022910862043963:ℚ)/22681238014556250000000000000000000000000000000000000000000000),((-74605179172552029236585023:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7348281529:ℚ)/10000000000),((3753787327:ℚ)/5000000000),((-2713787327:ℚ)/14537500000),((-13084844587:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((322612943:ℚ)/1250000000),((5541975749057228228420868312962941322670079907194568437173:ℚ)/111144609987500000000000000000000000000000000000000000000000),((-88006060023119105104082967:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((373366053:ℚ)/500000000),((96821211:ℚ)/125000000),((-70821211:ℚ)/369375000),((-672098159:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((233912301:ℚ)/1250000000),((42079871866736728198709560040385047012229059675834895431:ℚ)/838411068750000000000000000000000000000000000000000000000),((-287037772246872694705583:ℚ)/36966400000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((481585811:ℚ)/625000000),((4110915739:ℚ)/5000000000),((-3070915739:ℚ)/15250000000),((-884757433:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((381208471028334351174754044961985464567712006208377849:ℚ)/7504143750000000000000000000000000000000000000000000000),((-10021461:ℚ)/1024000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8181379403:ℚ)/10000000000),((5062644591:ℚ)/5000000000),((-4022644591:ℚ)/16200000000),((-15584138209:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((113155522399366585048987907958392139448731023208874830192991:ℚ)/2073600000000000000000000000000000000000000000000000000000000),((-10021461:ℚ)/1024000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10084446791:ℚ)/10000000000),((6964671857:ℚ)/5000000000),((-5924671857:ℚ)/20000000000),((-21293340373:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((113932443334338649310719013269721550611397092259602791027:ℚ)/1868851200000000000000000000000000000000000000000000000000),((-10021461:ℚ)/1024000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC13
#check @N11Formalization.C450Source15GroupedC13.bound
#print axioms N11Formalization.C450Source15GroupedC13.valid0
#print axioms N11Formalization.C450Source15GroupedC13.valid1
#print axioms N11Formalization.C450Source15GroupedC13.valid2
#print axioms N11Formalization.C450Source15GroupedC13.valid3
#print axioms N11Formalization.C450Source15GroupedC13.valid4
#print axioms N11Formalization.C450Source15GroupedC13.valid5
#print axioms N11Formalization.C450Source15GroupedC13.valid6
#print axioms N11Formalization.C450Source15GroupedC13.valid7
#print axioms N11Formalization.C450Source15GroupedC13.valid8
#print axioms N11Formalization.C450Source15GroupedC13.valid9
#print axioms N11Formalization.C450Source15GroupedC13.valid10
#print axioms N11Formalization.C450Source15GroupedC13.valid11
#print axioms N11Formalization.C450Source15GroupedC13.valid12
#print axioms N11Formalization.C450Source15GroupedC13.valid13
#print axioms N11Formalization.C450Source15GroupedC13.valid14
#print axioms N11Formalization.C450Source15GroupedC13.bound
#print axioms N11Formalization.C450Source15GroupedC13.endpoint_checks
