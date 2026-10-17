import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((5596253909:ℚ)/10000000000),((76807061:ℚ)/125000000),((27663766939:ℚ)/35600000000),((605649427:ℚ)/620000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7431377229:ℚ)/10000000000),((-21499820018024759192696851352628319649:ℚ)/281987600000000000000000000000000000000),((-38778971274787779354571:ℚ)/115520000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3035938539:ℚ)/5000000000),((6382423943:ℚ)/10000000000),((44587201007:ℚ)/55300000000),((16705655867:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6452803421:ℚ)/10000000000),((-1765672632166070640696432429141814470204053937690241177:ℚ)/20068715625000000000000000000000000000000000000000000000),((-245709721055557571243374899:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((788707061:ℚ)/1250000000),((6620259101:ℚ)/10000000000),((11533191793:ℚ)/14300000000),((51781813707:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2956488779:ℚ)/5000000000),((-805232989870716566591928662756530354327856493285255291:ℚ)/9138146875000000000000000000000000000000000000000000000),((-243229166747695693885053051:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1309483461:ℚ)/2000000000),((6739168451:ℚ)/10000000000),((19071284993:ℚ)/23260000000),((52614179157:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5325753669:ℚ)/10000000000),((-2755126807715686605423483203984516751431943256443971497:ℚ)/29494457756250000000000000000000000000000000000000000000),((-241987060187729002899784251:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6666291313:ℚ)/10000000000),((6858072667:ℚ)/10000000000),((96901787069:ℚ)/118200000000),((53446508669:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((500914847:ℚ)/1000000000),((-361333817497335865895385605196269903377687540435451518141:ℚ)/3870470081250000000000000000000000000000000000000000000000),((-666880140101827123430899:ℚ)/2048000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6785161327:ℚ)/10000000000),((1395394399:ℚ)/2000000000),((98447097251:ℚ)/120100000000),((3618586931:ℚ)/3940000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((584134559:ℚ)/1250000000),((-1515308697158538997596845355617099520873867835934511930811:ℚ)/16240533759375000000000000000000000000000000000000000000000),((-9579967020155167914846051:ℚ)/29573120000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((6904027539:ℚ)/10000000000),((886983333:ℚ)/1250000000),((99992358007:ℚ)/122000000000),((6888883331:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((539120137:ℚ)/1250000000),((-529173321010851231038171995164914745733498333921784769821:ℚ)/5674525000000000000000000000000000000000000000000000000000),((-3722709261341033831450539:ℚ)/11552000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((56183121:ℚ)/80000000),((7214756887:ℚ)/10000000000),((116042939:ℚ)/141600000),((55943298209:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3922154821:ℚ)/10000000000),((-68913730681841993289824762847898163259782915251:ℚ)/739364400000000000000000000000000000000000000000),((-237006380157404881899710419:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3570874627:ℚ)/5000000000),((7333642867:ℚ)/10000000000),((3031845303:ℚ)/3700000000),((56775500069:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((698066039:ℚ)/2000000000),((-14400977559250314936749735288049516164845753284021:ℚ)/154580688476562500000000000000000000000000000000000),((-235758135809316278377021339:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((3630302541:ℚ)/5000000000),((7571402847:ℚ)/10000000000),((52313933033:ℚ)/64800000000),((58439819929:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((119991493:ℚ)/400000000),((-2788180863937876446236793136952575352777464279640166473:ℚ)/31492800000000000000000000000000000000000000000000000000),((-233257944436491387020489059:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((3749153709:ℚ)/5000000000),((9473037579:ℚ)/10000000000),((53858998217:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1637714869:ℚ)/10000000000),((-13141776102537679479455182531425588020485429032759856057:ℚ)/300000000000000000000000000000000000000000000000000000000),((-80663741:ℚ)/256000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((9399579779:ℚ)/10000000000),((6637477801:ℚ)/5000000000),((44144845709:ℚ)/73600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-922150083684249552738624450828704141:ℚ)/49836032000000000000000000000000000000),((-80663741:ℚ)/256000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC30
#check @N11Formalization.C450Source18GroupedC30.bound
#print axioms N11Formalization.C450Source18GroupedC30.valid0
#print axioms N11Formalization.C450Source18GroupedC30.valid1
#print axioms N11Formalization.C450Source18GroupedC30.valid2
#print axioms N11Formalization.C450Source18GroupedC30.valid3
#print axioms N11Formalization.C450Source18GroupedC30.valid4
#print axioms N11Formalization.C450Source18GroupedC30.valid5
#print axioms N11Formalization.C450Source18GroupedC30.valid6
#print axioms N11Formalization.C450Source18GroupedC30.valid7
#print axioms N11Formalization.C450Source18GroupedC30.valid8
#print axioms N11Formalization.C450Source18GroupedC30.valid9
#print axioms N11Formalization.C450Source18GroupedC30.valid10
#print axioms N11Formalization.C450Source18GroupedC30.valid11
#print axioms N11Formalization.C450Source18GroupedC30.bound
#print axioms N11Formalization.C450Source18GroupedC30.endpoint_checks
