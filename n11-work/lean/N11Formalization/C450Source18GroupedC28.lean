import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((141841599:ℚ)/250000000),((621880057:ℚ)/1000000000),((1816257589:ℚ)/2670000000),((2137640171:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7279577959:ℚ)/10000000000),((-100836926533837522820187350777701:ℚ)/2379270375000000000000000000000000),((-2448080827315767516922181:ℚ)/7393280000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((15374573:ℚ)/25000000),((1614214609:ℚ)/2500000000),((194720303:ℚ)/276500000),((5522643827:ℚ)/6675000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((628027451:ℚ)/1000000000),((-129015354359739401397837251886235628636092264153:ℚ)/2508589453125000000000000000000000000000000000000),((-15243806128573047582620789:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((1277570313:ℚ)/2000000000),((6694879119:ℚ)/10000000000),((16101273443:ℚ)/22880000000),((22804637357:ℚ)/27650000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2862892057:ℚ)/5000000000),((-1935812083896569476471488298459106875225108538302818441:ℚ)/37429849600000000000000000000000000000000000000000000000),((-242980491545719105865917109:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6625839121:ℚ)/10000000000),((340693833:ℚ)/500000000),((83124230331:ℚ)/116300000000),((1158081499:ℚ)/1430000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1023777377:ℚ)/2000000000),((-68413478383348944626052509400335354786698343994248450537:ℚ)/1228935739843750000000000000000000000000000000000000000000),((-606288318933971233098341:ℚ)/1848320000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1686205229:ℚ)/2500000000),((6932866219:ℚ)/10000000000),((21108257519:ℚ)/29550000000),((23518598657:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2394781091:ℚ)/5000000000),((-3367796427131372081074282540876869436122674546052560791:ℚ)/60476095019531250000000000000000000000000000000000000000),((-242046855235560807880163309:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3431897619:ℚ)/5000000000),((7051848177:ℚ)/10000000000),((42870873809:ℚ)/60050000000),((23875544531:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4437897817:ℚ)/10000000000),((-113073070244736587690071506734983209640929180609729160369:ℚ)/2030066719921875000000000000000000000000000000000000000000),((-241575073687614346984587701:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((6982762443:ℚ)/10000000000),((896352861:ℚ)/1250000000),((87050386873:ℚ)/122000000000),((3029058583:ℚ)/3753125000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4058059687:ℚ)/10000000000),((-316086037554386195577925281109873414503007620904427361299:ℚ)/5674525000000000000000000000000000000000000000000000000000),((-3767187221111128831209149:ℚ)/11552000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((443857679:ℚ)/625000000),((7289790689:ℚ)/10000000000),((5522434469:ℚ)/7743750000),((24589372067:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((364120831:ℚ)/1000000000),((-2245158878625287812697992587726698277654951962227087:ℚ)/40308950614929199218750000000000000000000000000000000),((-240621579876244180608457749:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1444135363:ℚ)/2000000000),((3704375947:ℚ)/5000000000),((17933488993:ℚ)/25160000000),((12473127841:ℚ)/15487500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3172751027:ℚ)/10000000000),((-2706716187063742333827425739816637212775373945142211:ℚ)/48605115039062500000000000000000000000000000000000000),((-60034966542199356774667821:ℚ)/184832000000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((733962459:ℚ)/1000000000),((7646655677:ℚ)/10000000000),((9097587049:ℚ)/12960000000),((25659967031:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2625161073:ℚ)/10000000000),((-13193514709440494523507281574897108166974415275838921:ℚ)/251942400000000000000000000000000000000000000000000000),((-82880347:ℚ)/256000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((3788751351:ℚ)/5000000000),((2387298541:ℚ)/2500000000),((46796264861:ℚ)/80000000000),((7841895623:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((384813747:ℚ)/5000000000),((-5915659742736902992211769891388080804757036689584686309:ℚ)/300000000000000000000000000000000000000000000000000000000),((-82880347:ℚ)/256000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9479879877:ℚ)/10000000000),((2670434339:ℚ)/2000000000),((114518678647:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2346795589614859740292872620007491633:ℚ)/1345572864000000000000000000000000000000),((-82880347:ℚ)/256000000)⟩
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
end N11Formalization.C450Source18GroupedC28
#check @N11Formalization.C450Source18GroupedC28.bound
#print axioms N11Formalization.C450Source18GroupedC28.valid0
#print axioms N11Formalization.C450Source18GroupedC28.valid1
#print axioms N11Formalization.C450Source18GroupedC28.valid2
#print axioms N11Formalization.C450Source18GroupedC28.valid3
#print axioms N11Formalization.C450Source18GroupedC28.valid4
#print axioms N11Formalization.C450Source18GroupedC28.valid5
#print axioms N11Formalization.C450Source18GroupedC28.valid6
#print axioms N11Formalization.C450Source18GroupedC28.valid7
#print axioms N11Formalization.C450Source18GroupedC28.valid8
#print axioms N11Formalization.C450Source18GroupedC28.valid9
#print axioms N11Formalization.C450Source18GroupedC28.valid10
#print axioms N11Formalization.C450Source18GroupedC28.valid11
#print axioms N11Formalization.C450Source18GroupedC28.bound
#print axioms N11Formalization.C450Source18GroupedC28.endpoint_checks
