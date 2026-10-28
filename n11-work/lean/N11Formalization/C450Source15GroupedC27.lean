import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5801648929:ℚ)/10000000000),((6337645873:ℚ)/10000000000),((6633648929:ℚ)/10680000000),((78674104603:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7022746209:ℚ)/10000000000),((-2214814346041873836348570502503031:ℚ)/101515536000000000000000000000000000),((-97651098838205845345068179:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6277600841:ℚ)/10000000000),((1643892771:ℚ)/2500000000),((1015657263:ℚ)/1580000000),((20322820481:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5988221427:ℚ)/10000000000),((-677049033436229501297795406495900368861719520450457:ℚ)/24651950000000000000000000000000000000000000000000000),((-6110003146348420701668891:ℚ)/23104000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((1628881901:ℚ)/2500000000),((272538719:ℚ)/400000000),((1836881901:ℚ)/2860000000),((3356325909:ℚ)/4424000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5407821967:ℚ)/10000000000),((-4060491356722497891750973147488201691049616600152539:ℚ)/146210350000000000000000000000000000000000000000000000),((-156456912948899993775411:ℚ)/591462400000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((844178243:ℚ)/1250000000),((433275417:ℚ)/625000000),((948178243:ℚ)/1453750000),((5326029587:ℚ)/7150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4764935401:ℚ)/10000000000),((-145020505584718287435752202024753955180074263907197:ℚ)/4800530233764648437500000000000000000000000000000000),((-382180809507028829146939:ℚ)/1444000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((687236533:ℚ)/1000000000),((881417411:ℚ)/1250000000),((770436533:ℚ)/1182000000),((10815591521:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((22057809:ℚ)/50000000),((-26036904430247677270047119062879471848854572298521:ℚ)/860104462500000000000000000000000000000000000000000),((-1528903150408585856304371:ℚ)/5776000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((1747824653:ℚ)/2500000000),((7110803407:ℚ)/10000000000),((1955824653:ℚ)/2978750000),((87178837477:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4029512541:ℚ)/10000000000),((-5189210449082416202402285078153408679389719128501147:ℚ)/165189402917480468750000000000000000000000000000000000),((-97875721380585262128567699:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((440672691:ℚ)/625000000),((7170266113:ℚ)/10000000000),((492672691:ℚ)/750625000),((87832927243:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3825065703:ℚ)/10000000000),((-5191767225626194627809409520227066836574523631301:ℚ)/165207252597808837890625000000000000000000000000000),((-5151640389689210335591201:ℚ)/19456000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((3555113041:ℚ)/5000000000),((7229727439:ℚ)/10000000000),((1323704347:ℚ)/2017500000),((88487001829:ℚ)/120100000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3609660759:ℚ)/10000000000),((-537806095788932678546243305086268736092263976290431:ℚ)/17108005957031250000000000000000000000000000000000000),((-97886489192565961926945171:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((1792421931:ℚ)/2500000000),((3644593709:ℚ)/5000000000),((2000421931:ℚ)/3050000000),((44570530799:ℚ)/60525000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((422649967:ℚ)/1250000000),((-5575963918771583164624708134966347767038429203191581:ℚ)/177328906250000000000000000000000000000000000000000000),((-24472921689457574671625131:ℚ)/92416000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7229148013:ℚ)/10000000000),((7408103459:ℚ)/10000000000),((8061148013:ℚ)/12390000000),((90449138049:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3136826651:ℚ)/10000000000),((-30119523868939531323501504736996885090154969384001089:ℚ)/990632770312500000000000000000000000000000000000000000),((-97881362659829205077613131:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((7348064659:ℚ)/10000000000),((7527014473:ℚ)/10000000000),((8180064659:ℚ)/12580000000),((91757159203:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2582021319:ℚ)/10000000000),((-369783076946517498233397463034749121661421846444301:ℚ)/12151278759765625000000000000000000000000000000000000),((-97890889277891654792823779:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7466976261:ℚ)/10000000000),((970602789:ℚ)/1250000000),((8298976261:ℚ)/12960000000),((11796630679:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((74949419:ℚ)/400000000),((-4787788078305719944994265338584239737578829717108899:ℚ)/167961600000000000000000000000000000000000000000000000),((-51532739625534883:ℚ)/194560000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((7704785223:ℚ)/10000000000),((302086183:ℚ)/312500000),((8536785223:ℚ)/16000000000),((133442519:ℚ)/150000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-14551956028373257708970868741800768790295187080684313:ℚ)/1600000000000000000000000000000000000000000000000000000),((-211993:ℚ)/800000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((4803363913:ℚ)/5000000000),((6734514301:ℚ)/5000000000),((1739787971:ℚ)/3680000000),((78559657311:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((31577057997896504403969:ℚ)/6771200000000000000000000),((-211993:ℚ)/800000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC27
#check @N11Formalization.C450Source15GroupedC27.bound
#print axioms N11Formalization.C450Source15GroupedC27.valid0
#print axioms N11Formalization.C450Source15GroupedC27.valid1
#print axioms N11Formalization.C450Source15GroupedC27.valid2
#print axioms N11Formalization.C450Source15GroupedC27.valid3
#print axioms N11Formalization.C450Source15GroupedC27.valid4
#print axioms N11Formalization.C450Source15GroupedC27.valid5
#print axioms N11Formalization.C450Source15GroupedC27.valid6
#print axioms N11Formalization.C450Source15GroupedC27.valid7
#print axioms N11Formalization.C450Source15GroupedC27.valid8
#print axioms N11Formalization.C450Source15GroupedC27.valid9
#print axioms N11Formalization.C450Source15GroupedC27.valid10
#print axioms N11Formalization.C450Source15GroupedC27.valid11
#print axioms N11Formalization.C450Source15GroupedC27.valid12
#print axioms N11Formalization.C450Source15GroupedC27.valid13
#print axioms N11Formalization.C450Source15GroupedC27.bound
#print axioms N11Formalization.C450Source15GroupedC27.endpoint_checks
