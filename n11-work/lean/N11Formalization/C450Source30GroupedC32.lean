import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2519999999:ℚ)/5000000000),((5375691113:ℚ)/10000000000),((9351999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8457663309:ℚ)/10000000000),((-198996370149736354108224572685336421:ℚ)/530450000000000000000000000000000000),((-71521246200959531344761937:ℚ)/147865600000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2638749999:ℚ)/5000000000),((5613612011:ℚ)/10000000000),((9708249997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((4015998001:ℚ)/5000000000),((-11944690187172980640498267646661179:ℚ)/31684000000000000000000000000000000),((-70427846289836035311261937:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2757499999:ℚ)/5000000000),((1433140349:ℚ)/2500000000),((10064499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7588062497:ℚ)/10000000000),((-229060443785232911511489427822797889:ℚ)/590784500000000000000000000000000000),((-70136089789060191253761937:ℚ)/147865600000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2816874999:ℚ)/5000000000),((1170300783:ℚ)/2000000000),((10242624997:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3679083077:ℚ)/5000000000),((-4240802019186803069166272976320899:ℚ)/10921750000000000000000000000000000),((-69608310288175422972011937:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((2876249999:ℚ)/5000000000),((1194087983:ℚ)/2000000000),((10420749997:ℚ)/11250000000),(1:ℚ),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((7122277169:ℚ)/10000000000),((-189851983802251542622976521438729:ℚ)/488281250000000000000000000000000),((-69085945786675717828261937:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2935624999:ℚ)/5000000000),((6029905573:ℚ)/10000000000),((10598874997:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6879758289:ℚ)/10000000000),((-12669675017013093530277142924106617:ℚ)/32177256250000000000000000000000000),((-68958929658820023918511937:ℚ)/147865600000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((2965312499:ℚ)/5000000000),((6089369723:ℚ)/10000000000),((10687937497:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((675578377:ℚ)/1000000000),((-257780256584862576030718833512750011:ℚ)/654368000000000000000000000000000000),((-68702473374127527640386937:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2994999999:ℚ)/5000000000),((15372081:ℚ)/25000000),((10776999997:ℚ)/11535000000),(1:ℚ),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6629860831:ℚ)/10000000000),((-34140831701207919212820749360081:ℚ)/86625146484375000000000000000000),((-68447369811394872570761937:ℚ)/147865600000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3024687499:ℚ)/5000000000),((3104146821:ℚ)/5000000000),((10866062497:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3250936821:ℚ)/5000000000),((-266657450739765885365669011134457403:ℚ)/676284500000000000000000000000000000),((-68193618721437470933636937:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3054374999:ℚ)/5000000000),((1566938371:ℚ)/2500000000),((10955124997:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((6371695167:ℚ)/10000000000),((-271147803601404549179495696107745803:ℚ)/687378125000000000000000000000000000),((-67941219874743202409011937:ℚ)/147865600000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3084062499:ℚ)/5000000000),((6327211959:ℚ)/10000000000),((11044187497:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((6239185573:ℚ)/10000000000),((-45945433777267188036628418221397467:ℚ)/116427000000000000000000000000000000),((-67690173054914924980886937:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3113749999:ℚ)/5000000000),((63866691:ℚ)/100000000),((11133249997:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((6104190351:ℚ)/10000000000),((-280231803967292977125141901110396353:ℚ)/709836125000000000000000000000000000),((-67440478045555496633261937:ℚ)/147865600000000000000000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3143437499:ℚ)/5000000000),((6446124939:ℚ)/10000000000),((11222312497:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2983269027:ℚ)/5000000000),((-142412681507898645325586580810615941:ℚ)/360600250000000000000000000000000000),((-67192134636825264502136937:ℚ)/147865600000000000000000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3173124999:ℚ)/5000000000),((3252789753:ℚ)/5000000000),((11311374997:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((5826037581:ℚ)/10000000000),((-5360245087498299701040538627955383:ℚ)/13567687500000000000000000000000000),((-66945142631999554027511937:ℚ)/147865600000000000000000000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3202812499:ℚ)/5000000000),((51289319:ℚ)/78125000),((11400437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((355154679:ℚ)/625000000),((-294115373447372551023815128888891631:ℚ)/744200000000000000000000000000000000),((-66699501827796201497386937:ℚ)/147865600000000000000000000)⟩
theorem valid14 : Valid source30 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source30 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3232499999:ℚ)/5000000000),((3341967937:ℚ)/5000000000),((11489499997:ℚ)/12390000000),(1:ℚ),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1383902201:ℚ)/2500000000),((-100108044390521163885850341616636231:ℚ)/255853500000000000000000000000000000),((-66065363218611688447761937:ℚ)/147865600000000000000000000)⟩
theorem valid15 : Valid source30 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3291874999:ℚ)/5000000000),((1700708571:ℚ)/2500000000),((11667624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2615417823:ℚ)/5000000000),((-154924818937291307622161360837740433:ℚ)/395641000000000000000000000000000000),((-65580850970922175734011937:ℚ)/147865600000000000000000000)⟩
theorem valid16 : Valid source30 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source30 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3351249999:ℚ)/5000000000),((3520309013:ℚ)/5000000000),((11845749997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4909022139:ℚ)/10000000000),((-107548039579797925535037591476999683:ℚ)/279936000000000000000000000000000000),((-64322121699424025806261937:ℚ)/147865600000000000000000000)⟩
theorem valid17 : Valid source30 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source30 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3469999999:ℚ)/5000000000),((7991603843:ℚ)/10000000000),((12201999997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((1049577159:ℚ)/2500000000),((-361595497723189405805990836038693251:ℚ)/1048352000000000000000000000000000000),((-61271167300812157220761937:ℚ)/147865600000000000000000000)⟩
theorem valid18 : Valid source30 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3944999999:ℚ)/5000000000),((2235600529:ℚ)/2500000000),((13626999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-448551618700167554914243393603829491:ℚ)/1280000000000000000000000000000000000),((-436974587:ℚ)/1024000000)⟩
theorem valid19 : Valid source30 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source30 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4419999999:ℚ)/5000000000),((12744495281:ℚ)/10000000000),((15051999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-20376040173250966904110277:ℚ)/81254400000000000000000000),((-436974587:ℚ)/1024000000)⟩
theorem valid20 : Valid source30 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source30 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source30 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source30 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source30 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC32
#check @N11Formalization.C450Source30GroupedC32.bound
#print axioms N11Formalization.C450Source30GroupedC32.valid0
#print axioms N11Formalization.C450Source30GroupedC32.valid1
#print axioms N11Formalization.C450Source30GroupedC32.valid2
#print axioms N11Formalization.C450Source30GroupedC32.valid3
#print axioms N11Formalization.C450Source30GroupedC32.valid4
#print axioms N11Formalization.C450Source30GroupedC32.valid5
#print axioms N11Formalization.C450Source30GroupedC32.valid6
#print axioms N11Formalization.C450Source30GroupedC32.valid7
#print axioms N11Formalization.C450Source30GroupedC32.valid8
#print axioms N11Formalization.C450Source30GroupedC32.valid9
#print axioms N11Formalization.C450Source30GroupedC32.valid10
#print axioms N11Formalization.C450Source30GroupedC32.valid11
#print axioms N11Formalization.C450Source30GroupedC32.valid12
#print axioms N11Formalization.C450Source30GroupedC32.valid13
#print axioms N11Formalization.C450Source30GroupedC32.valid14
#print axioms N11Formalization.C450Source30GroupedC32.valid15
#print axioms N11Formalization.C450Source30GroupedC32.valid16
#print axioms N11Formalization.C450Source30GroupedC32.valid17
#print axioms N11Formalization.C450Source30GroupedC32.valid18
#print axioms N11Formalization.C450Source30GroupedC32.valid19
#print axioms N11Formalization.C450Source30GroupedC32.valid20
#print axioms N11Formalization.C450Source30GroupedC32.bound
#print axioms N11Formalization.C450Source30GroupedC32.endpoint_checks
