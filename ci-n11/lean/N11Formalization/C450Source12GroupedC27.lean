import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((1472315289:ℚ)/2500000000),((802211579:ℚ)/1250000000),((1632315289:ℚ)/2670000000),((9704327369:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6842350503:ℚ)/10000000000),((-506359159178449088496772686709:ℚ)/33045421875000000000000000000000),((-114417180957001771360878121:ℚ)/554496000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((318242407:ℚ)/500000000),((166386099:ℚ)/250000000),((350242407:ℚ)/553000000),((2006247089:ℚ)/2670000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1445352327:ℚ)/2500000000),((-1251128108617364880152004464970357075193246973841:ℚ)/66059522265625000000000000000000000000000000000000),((-1528379497471571772323683:ℚ)/7393280000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((6602611329:ℚ)/10000000000),((6774313247:ℚ)/10000000000),((7242611329:ℚ)/11250000000),((81557445717:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5180940159:ℚ)/10000000000),((-424377508844362912824983408091953595737787231415421:ℚ)/20599365234375000000000000000000000000000000000000000),((-1835774706978740227440342841:ℚ)/8871936000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((3360743123:ℚ)/5000000000),((6893178567:ℚ)/10000000000),((3680743123:ℚ)/5720000000),((82864964237:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((303485243:ℚ)/625000000),((-137374635360040140830767132016398286996786671979711:ℚ)/6645925000000000000000000000000000000000000000000000),((-423970828987638838454163:ℚ)/2048000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3420178503:ℚ)/5000000000),((7012040113:ℚ)/10000000000),((3740178503:ℚ)/5815000000),((7652040113:ℚ)/10400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1127297583:ℚ)/2500000000),((-398104445296079963549837799025031316016454850347009:ℚ)/19202120935058593750000000000000000000000000000000000),((-459378350733174758949474409:ℚ)/2217984000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((869902977:ℚ)/1250000000),((883933691:ℚ)/1250000000),((949902977:ℚ)/1465625000),((10603270601:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((4135814513:ℚ)/10000000000),((-943756641306712101236050452122356328452548060737:ℚ)/43920835852622985839843750000000000000000000000000),((-28724844113633994085967929:ℚ)/138624000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((7018655799:ℚ)/10000000000),((1782724517:ℚ)/2500000000),((7658655799:ℚ)/11820000000),((21369969687:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3936705237:ℚ)/10000000000),((-128452232790570746531116095455034724417162748227051:ℚ)/5972947656250000000000000000000000000000000000000000),((-1838830151948062376878341001:ℚ)/8871936000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((442380429:ℚ)/625000000),((898790719:ℚ)/1250000000),((482380429:ℚ)/744687500),((3588899303:ℚ)/4925000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3727559317:ℚ)/10000000000),((-3471922330942895911129220509291887070820137096183:ℚ)/161317776286602020263671875000000000000000000000000),((-7184654269944824641700641:ℚ)/34656000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1427503407:ℚ)/2000000000),((7249752603:ℚ)/10000000000),((1555503407:ℚ)/2402000000),((86787278633:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3506577221:ℚ)/10000000000),((-7287083421382347308962205032176543020084928553841:ℚ)/338344453320312500000000000000000000000000000000000),((-73588561874739141012825049:ℚ)/354877440000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((7196946331:ℚ)/10000000000),((3654589319:ℚ)/5000000000),((7836946331:ℚ)/12105000000),((43720482509:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3271356861:ℚ)/10000000000),((-553050847293136010377525908759636234776259458609831:ℚ)/25662008935546875000000000000000000000000000000000000),((-1699130021535476184247267:ℚ)/8192000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((3628187387:ℚ)/5000000000),((7368603877:ℚ)/10000000000),((3948187387:ℚ)/6100000000),((88094642647:ℚ)/121050000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((603713373:ℚ)/2000000000),((-31343492205053786435517001952300587350299942846161:ℚ)/1453515625000000000000000000000000000000000000000000),((-153383566048358616951605723:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((457237649:ℚ)/625000000),((3743726021:ℚ)/5000000000),((165745883:ℚ)/258125000),((44700986231:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2743349511:ℚ)/10000000000),((-35127201866945188924325567601708240640887560789:ℚ)/1679539608955383300781250000000000000000000000000),((-2397199198878252073313267:ℚ)/11552000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((371732759:ℚ)/500000000),((3803148619:ℚ)/5000000000),((403732759:ℚ)/629000000),((15118211603:ℚ)/20650000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2089748541:ℚ)/10000000000),((-1988424616087819094460595152998006742816296977:ℚ)/94931865310668945312500000000000000000000000000),((-1534954173432680443644227:ℚ)/7393280000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((3776752433:ℚ)/5000000000),((3921989623:ℚ)/5000000000),((4096752433:ℚ)/6480000000),((46661885853:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1106709437:ℚ)/10000000000),((-8634610615386950880662877782960163669854592065957:ℚ)/437400000000000000000000000000000000000000000000000),((-153570490348455051378406963:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((7791195461:ℚ)/10000000000),((4872561907:ℚ)/5000000000),((8431195461:ℚ)/16000000000),((6346464553:ℚ)/7200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-738388124930494133739934720940216394864693027873843:ℚ)/100000000000000000000000000000000000000000000000000000),((-212742341:ℚ)/1024000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((4846197003:ℚ)/5000000000),((6773233471:ℚ)/5000000000),((224617261:ℚ)/480000000),((78025568181:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2392667252678345251:ℚ)/1920000000000000000000),((-212742341:ℚ)/1024000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC27
#check @N11Formalization.C450Source12GroupedC27.bound
#print axioms N11Formalization.C450Source12GroupedC27.valid0
#print axioms N11Formalization.C450Source12GroupedC27.valid1
#print axioms N11Formalization.C450Source12GroupedC27.valid2
#print axioms N11Formalization.C450Source12GroupedC27.valid3
#print axioms N11Formalization.C450Source12GroupedC27.valid4
#print axioms N11Formalization.C450Source12GroupedC27.valid5
#print axioms N11Formalization.C450Source12GroupedC27.valid6
#print axioms N11Formalization.C450Source12GroupedC27.valid7
#print axioms N11Formalization.C450Source12GroupedC27.valid8
#print axioms N11Formalization.C450Source12GroupedC27.valid9
#print axioms N11Formalization.C450Source12GroupedC27.valid10
#print axioms N11Formalization.C450Source12GroupedC27.valid11
#print axioms N11Formalization.C450Source12GroupedC27.valid12
#print axioms N11Formalization.C450Source12GroupedC27.valid13
#print axioms N11Formalization.C450Source12GroupedC27.valid14
#print axioms N11Formalization.C450Source12GroupedC27.valid15
#print axioms N11Formalization.C450Source12GroupedC27.bound
#print axioms N11Formalization.C450Source12GroupedC27.endpoint_checks
