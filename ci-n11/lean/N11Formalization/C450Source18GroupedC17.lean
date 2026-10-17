import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((30601217:ℚ)/50000000),((3322123757:ℚ)/5000000000),((128:ℚ)/1335),((8762123757:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3173115701:ℚ)/5000000000),((67593104218434017633194181595219474398267:ℚ)/1087370546688000000000000000000000000000000),((-27912339437878812926991791:ℚ)/184832000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((1319581793:ℚ)/2000000000),((5506247:ℚ)/8000000),((256:ℚ)/2765),((4736749:ℚ)/28480000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1038684091:ℚ)/2000000000),((3949274706582553885084598320020467749446768779637379:ℚ)/66227977703731200000000000000000000000000000000000000),((-77015700191736166439:ℚ)/473169920000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((3418301659:ℚ)/5000000000),((700206231:ℚ)/1000000000),((512:ℚ)/5625),((255458033:ℚ)/1580000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4520510611:ℚ)/10000000000),((741145700634058581857678755516112567337202829564891:ℚ)/12638025000000000000000000000000000000000000000000000),((-1246771036426391783763399:ℚ)/7393280000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((347796001:ℚ)/500000000),((7121299041:ℚ)/10000000000),((64:ℚ)/715),((18001299041:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4146617823:ℚ)/10000000000),((5307081868134974256870653688189315424562434259608778758778533:ℚ)/90987066650390625000000000000000000000000000000000000000000000),((-126821888324721907784880279:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7075217767:ℚ)/10000000000),((3620259887:ℚ)/5000000000),((512:ℚ)/5815),((9060259887:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((186895581:ℚ)/500000000),((11478240895592619461167368124817875729471423180345446061613851:ℚ)/197759586889150000000000000000000000000000000000000000000000000),((-32241377789455781988889271:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7194497497:ℚ)/10000000000),((3679862643:ℚ)/5000000000),((256:ℚ)/2955),((9119862643:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3281369571:ℚ)/10000000000),((1033456637774410760108344071543043022333813785056589704573413:ℚ)/17885162672848535156250000000000000000000000000000000000000000),((-32776997346258767686305391:ℚ)/184832000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7313760087:ℚ)/10000000000),((1495783261:ℚ)/2000000000),((512:ℚ)/6005),((3671783261:ℚ)/23640000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((688312873:ℚ)/2500000000),((10281371958780412664165577781188821004161263924014978977661659:ℚ)/178648637301282600000000000000000000000000000000000000000000000),((-5329973565113462008156239:ℚ)/29573120000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((1858251589:ℚ)/2500000000),((7598093513:ℚ)/10000000000),((128:ℚ)/1525),((18478093513:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2100180491:ℚ)/10000000000),((1155110441902903592856120733976411810430003554062217992091461:ℚ)/20143675372878125000000000000000000000000000000000000000000000),((-135389575441616875262404871:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7552237073:ℚ)/10000000000),((8074676467:ℚ)/10000000000),((32:ℚ)/405),((18954676467:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((560856017:ℚ)/5000000000),((537407865925590552835315150703065824709626723169685751882959:ℚ)/9307639631250000000000000000000000000000000000000000000000000),((-90513495228322517:ℚ)/486400000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((802901821:ℚ)/1000000000),((2494874747:ℚ)/2500000000),((8:ℚ)/125),((5214874747:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1174465391012765458248523818182528043775167359938759453:ℚ)/19929037500000000000000000000000000000000000000000000000),((-47942701:ℚ)/256000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((993444373:ℚ)/1000000000),((6892575717:ℚ)/5000000000),((16:ℚ)/345),((12332575717:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((20216377026492759480870115293812707409203:ℚ)/304704000000000000000000000000000000000000),((-47942701:ℚ)/256000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC17
#check @N11Formalization.C450Source18GroupedC17.bound
#print axioms N11Formalization.C450Source18GroupedC17.valid0
#print axioms N11Formalization.C450Source18GroupedC17.valid1
#print axioms N11Formalization.C450Source18GroupedC17.valid2
#print axioms N11Formalization.C450Source18GroupedC17.valid3
#print axioms N11Formalization.C450Source18GroupedC17.valid4
#print axioms N11Formalization.C450Source18GroupedC17.valid5
#print axioms N11Formalization.C450Source18GroupedC17.valid6
#print axioms N11Formalization.C450Source18GroupedC17.valid7
#print axioms N11Formalization.C450Source18GroupedC17.valid8
#print axioms N11Formalization.C450Source18GroupedC17.valid9
#print axioms N11Formalization.C450Source18GroupedC17.valid10
#print axioms N11Formalization.C450Source18GroupedC17.bound
#print axioms N11Formalization.C450Source18GroupedC17.endpoint_checks
