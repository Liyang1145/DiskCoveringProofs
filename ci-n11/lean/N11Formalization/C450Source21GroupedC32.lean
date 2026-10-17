import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2699999999:ℚ)/5000000000),((5957258713:ℚ)/10000000000),((9315999997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3902752213:ℚ)/5000000000),((-117353082010430590157659467422917967173432216924209199:ℚ)/634472100000000000000000000000000000000000000000000000),((-253722749414956662040786687:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2937499999:ℚ)/5000000000),((6194938927:ℚ)/10000000000),((10028499997:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1717995973:ℚ)/2500000000),((-27651760391771376107578949623231099664477229479688093:ℚ)/132119044531250000000000000000000000000000000000000000),((-248243199639240747235786687:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3056249999:ℚ)/5000000000),((6432607157:ℚ)/10000000000),((10384749997:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((3181698323:ℚ)/5000000000),((-1958209969348124217247138647879894248979980899682755197:ℚ)/9357462400000000000000000000000000000000000000000000000),((-242270609731649862973286687:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3174999999:ℚ)/5000000000),((1310287429:ℚ)/2000000000),((10740999997:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2908531719:ℚ)/5000000000),((-2168836130858765003915617051229224815210213805997272013:ℚ)/9831485918750000000000000000000000000000000000000000000),((-239586580552907051150786687:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3234374999:ℚ)/5000000000),((6670264559:ℚ)/10000000000),((10919124997:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2763108017:ℚ)/5000000000),((-189558750446181009753363909792956151418868762789850319:ℚ)/860104462500000000000000000000000000000000000000000000),((-236619883434817898964536687:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3293749999:ℚ)/5000000000),((336483867:ℚ)/500000000),((11097249997:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2610474967:ℚ)/5000000000),((-2388027034692515852845579577100591133931348192429305413:ℚ)/10572121786718750000000000000000000000000000000000000000),((-235291796566572688088286687:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3323437499:ℚ)/5000000000),((3394544761:ℚ)/5000000000),((11186312497:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5062091987:ℚ)/10000000000),((-611006743812761417874687127741364487145805299063736217:ℚ)/2706755626562500000000000000000000000000000000000000000),((-233813343336701166401411687:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3353124999:ℚ)/5000000000),((6848501119:ℚ)/10000000000),((11275374997:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((4898545211:ℚ)/10000000000),((-625238517956869442679124092299035940132531380049934317:ℚ)/2771496965039062500000000000000000000000000000000000000),((-232336292875556936602036687:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3382812499:ℚ)/5000000000),((6907912147:ℚ)/10000000000),((11364437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1182455021:ℚ)/2500000000),((-2558817779235102190460005575293801829515449669583341977:ℚ)/11349050000000000000000000000000000000000000000000000000),((-230860644743365913570161687:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3412499999:ℚ)/5000000000),((6967322617:ℚ)/10000000000),((11453499997:ℚ)/12295000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((1138834499:ℚ)/2500000000),((-163601724916401752284059548107369263483641893227546293:ℚ)/726015067333984375000000000000000000000000000000000000),((-229386398637783413785786687:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3442187499:ℚ)/5000000000),((7026732543:ℚ)/10000000000),((11542562497:ℚ)/12390000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((2187203387:ℚ)/5000000000),((-297488119753687560277545222771153288428248735415943377:ℚ)/1320843693750000000000000000000000000000000000000000000),((-227913554174007112768911687:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3471874999:ℚ)/5000000000),((714555081:ℚ)/1000000000),((11631624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4186186831:ℚ)/10000000000),((-683720824126440326552589396597724599713722935734976573:ℚ)/3110727362500000000000000000000000000000000000000000000),((-224809205848982367319536687:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3531249999:ℚ)/5000000000),((1452873409:ℚ)/2000000000),((11809749997:ℚ)/12770000000),(1:ℚ),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((756694989:ℚ)/2000000000),((-178717565643779525317223912673941977894539745966094117:ℚ)/813453489453125000000000000000000000000000000000000000),((-221870549785295406163286687:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3590624999:ℚ)/5000000000),((922897667:ℚ)/1250000000),((11987874997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1667516577:ℚ)/5000000000),((-332005962817344341011645100730646423994313734741927573:ℚ)/1511654400000000000000000000000000000000000000000000000),((-218937493912109005837036687:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3649999999:ℚ)/5000000000),((7858420679:ℚ)/10000000000),((12165999997:ℚ)/13720000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((22024087:ℚ)/78125000),((-121152455647898074122650771047764982380854833642853:ℚ)/630525109375000000000000000000000000000000000000000),((-213316248329757184900786687:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid source21 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3887499999:ℚ)/5000000000),((4166817441:ℚ)/5000000000),((12878499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-3677291090267250839018397458624462156715509313217745357:ℚ)/18975171200000000000000000000000000000000000000000000000),((-296669489:ℚ)/1024000000)⟩
theorem valid15 : Valid source21 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source21 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4124999999:ℚ)/5000000000),((9284002203:ℚ)/10000000000),((13590999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-1070666657274478513112226147528313606873192859298642277:ℚ)/6400000000000000000000000000000000000000000000000000000),((-296669489:ℚ)/1024000000)⟩
theorem valid16 : Valid source21 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source21 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4599999999:ℚ)/5000000000),((1635620697:ℚ)/1250000000),((15015999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-59244505427794964979545331607642277:ℚ)/897048576000000000000000000000000000),((-296669489:ℚ)/1024000000)⟩
theorem valid17 : Valid source21 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2383:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((61:ℚ)/80) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source21 nn0 nn1 Qcell ((1239:ℚ)/1600) ((1277:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((1277:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source21 nn0 nn1 Qcell ((1277:ℚ)/1600) ((343:ℚ)/400) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source21 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source21 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source21 nn0 nn1 Qcell ((1277:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC32
#check @N11Formalization.C450Source21GroupedC32.bound
#print axioms N11Formalization.C450Source21GroupedC32.valid0
#print axioms N11Formalization.C450Source21GroupedC32.valid1
#print axioms N11Formalization.C450Source21GroupedC32.valid2
#print axioms N11Formalization.C450Source21GroupedC32.valid3
#print axioms N11Formalization.C450Source21GroupedC32.valid4
#print axioms N11Formalization.C450Source21GroupedC32.valid5
#print axioms N11Formalization.C450Source21GroupedC32.valid6
#print axioms N11Formalization.C450Source21GroupedC32.valid7
#print axioms N11Formalization.C450Source21GroupedC32.valid8
#print axioms N11Formalization.C450Source21GroupedC32.valid9
#print axioms N11Formalization.C450Source21GroupedC32.valid10
#print axioms N11Formalization.C450Source21GroupedC32.valid11
#print axioms N11Formalization.C450Source21GroupedC32.valid12
#print axioms N11Formalization.C450Source21GroupedC32.valid13
#print axioms N11Formalization.C450Source21GroupedC32.valid14
#print axioms N11Formalization.C450Source21GroupedC32.valid15
#print axioms N11Formalization.C450Source21GroupedC32.valid16
#print axioms N11Formalization.C450Source21GroupedC32.valid17
#print axioms N11Formalization.C450Source21GroupedC32.bound
#print axioms N11Formalization.C450Source21GroupedC32.endpoint_checks
