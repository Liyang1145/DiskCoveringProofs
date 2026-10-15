import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5561978593:ℚ)/10000000000),((764714257:ℚ)/1250000000),((6905978593:ℚ)/10680000000),((10171856827:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1499558601:ℚ)/2000000000),((-2854475257047749562269987746273921:ℚ)/25378884000000000000000000000000000),((-66278837076716970091173:ℚ)/180500000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3019669847:ℚ)/5000000000),((6356328453:ℚ)/10000000000),((3691669847:ℚ)/5530000000),((83999612983:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3261827867:ℚ)/5000000000),((-34556752890619875907168825563801855560398532770799591:ℚ)/264238089062500000000000000000000000000000000000000000),((-50668315086736346559318541:ℚ)/138624000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((3138948867:ℚ)/5000000000),((6475607231:ℚ)/10000000000),((423438763:ℚ)/625000000),((85311679541:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2993764173:ℚ)/5000000000),((-53100592761805868774031852889249626013837598440331:ℚ)/381469726562500000000000000000000000000000000000000),((-16848557732020850924099463:ℚ)/46208000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6397149779:ℚ)/10000000000),((659486833:ℚ)/1000000000),((703740889:ℚ)/1040000000),((962483907:ℚ)/1250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((22812653:ℚ)/40000000),((-244356632353195539050328688697596579102080572082977:ℚ)/1757600000000000000000000000000000000000000000000000),((-167926044362336232027287:ℚ)/462080000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1303277009:ℚ)/2000000000),((53712901:ℚ)/80000000),((1572077009:ℚ)/2326000000),((63952901:ℚ)/83200000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2702815021:ℚ)/5000000000),((-682529958508348614955418977858190852645585590892513:ℚ)/4915742959375000000000000000000000000000000000000000),((-1071064723798113187183:ℚ)/2957312000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3317802181:ℚ)/5000000000),((6833340933:ℚ)/10000000000),((3989802181:ℚ)/5910000000),((89246750263:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2546296747:ℚ)/5000000000),((-11180162091173963078067144444977340980873238782234813:ℚ)/80634793359375000000000000000000000000000000000000000),((-50030710457342750043541261:ℚ)/138624000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((844351063:ℚ)/1250000000),((6952554019:ℚ)/10000000000),((1012351063:ℚ)/1501250000),((30186031403:ℚ)/39400000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1190241921:ℚ)/2500000000),((-731919413103343868196760834050598471482254872718719:ℚ)/5286632083129882812500000000000000000000000000000000),((-16617156090895699962494463:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((6873998197:ℚ)/10000000000),((3535876299:ℚ)/5000000000),((8217998197:ℚ)/12200000000),((45934639289:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((550815913:ℚ)/1250000000),((-392200887955833446173620206473310307855552427247493701:ℚ)/2837262500000000000000000000000000000000000000000000000),((-12417108182566927552728349:ℚ)/34656000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((174829353:ℚ)/250000000),((28089599:ℚ)/39062500),((69476451:ℚ)/103250000),((363985589:ℚ)/476562500),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2011607357:ℚ)/5000000000),((-59337773762557794733910578137533817260887905627:ℚ)/429962139892578125000000000000000000000000000000),((-32214586039983195873449:ℚ)/90250000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((7112336913:ℚ)/10000000000),((913763611:ℚ)/1250000000),((8456336913:ℚ)/12580000000),((11811399721:ℚ)/15487500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1800894253:ℚ)/5000000000),((-24619199217908780966104614049750055068131941110353:ℚ)/178695275878906250000000000000000000000000000000000),((-64180967273278561240067:ℚ)/180500000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7231487173:ℚ)/10000000000),((1887103677:ℚ)/2500000000),((8575487173:ℚ)/12960000000),((24278140447:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((195427283:ℚ)/625000000),((-5478944394218217380938576376880300185869233215320501:ℚ)/41990400000000000000000000000000000000000000000000000),((-3053562018846876213598921:ℚ)/8664000000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((1867438079:ℚ)/2500000000),((9453478093:ℚ)/10000000000),((2203438079:ℚ)/4000000000),((13118695447:ℚ)/14400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((927012113:ℚ)/5000000000),((-369234211984587629082430850761632341764759980671447:ℚ)/6250000000000000000000000000000000000000000000000000),((-42837562976281733:ℚ)/121600000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9374560359:ℚ)/10000000000),((2651882479:ℚ)/2000000000),((3572853453:ℚ)/7360000000),((31986707269:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-8488995558068712902667:ℚ)/846400000000000000000000),((-22566967:ℚ)/64000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC27
#check @N11Formalization.C450Source23GroupedC27.bound
#print axioms N11Formalization.C450Source23GroupedC27.valid0
#print axioms N11Formalization.C450Source23GroupedC27.valid1
#print axioms N11Formalization.C450Source23GroupedC27.valid2
#print axioms N11Formalization.C450Source23GroupedC27.valid3
#print axioms N11Formalization.C450Source23GroupedC27.valid4
#print axioms N11Formalization.C450Source23GroupedC27.valid5
#print axioms N11Formalization.C450Source23GroupedC27.valid6
#print axioms N11Formalization.C450Source23GroupedC27.valid7
#print axioms N11Formalization.C450Source23GroupedC27.valid8
#print axioms N11Formalization.C450Source23GroupedC27.valid9
#print axioms N11Formalization.C450Source23GroupedC27.valid10
#print axioms N11Formalization.C450Source23GroupedC27.valid11
#print axioms N11Formalization.C450Source23GroupedC27.valid12
#print axioms N11Formalization.C450Source23GroupedC27.bound
#print axioms N11Formalization.C450Source23GroupedC27.endpoint_checks
