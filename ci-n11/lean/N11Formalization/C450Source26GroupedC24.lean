import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5639218189:ℚ)/10000000000),((1239788881:ℚ)/2000000000),((54834527323:ℚ)/106800000000),((1639788881:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3673720047:ℚ)/5000000000),((-15461329886735204006713250266986845809:ℚ)/304546608000000000000000000000000000000),((-4728862992476182454597:ℚ)/11552000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3059290897:ℚ)/5000000000),((6438385837:ℚ)/10000000000),((29095036279:ℚ)/55300000000),((2812795279:ℚ)/4450000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1587479537:ℚ)/2500000000),((-209565977221469933081311873696693926261675019692504525917:ℚ)/3170857068750000000000000000000000000000000000000000000000),((-120714135205737647741613:ℚ)/288800000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((3179017943:ℚ)/5000000000),((819757099:ℚ)/1250000000),((29933125601:ℚ)/56250000000),((1069757099:ℚ)/1728125000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1159558269:ℚ)/2000000000),((-27012534501122968910494094017638401116078619798254601723:ℚ)/370788574218750000000000000000000000000000000000000000000),((-1905346410302674352877:ℚ)/4512500000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((1619428211:ℚ)/2500000000),((1669424203:ℚ)/2500000000),((15175997477:ℚ)/28600000000),((723141401:ℚ)/1171875000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((687963533:ℚ)/1250000000),((-968535738779907889097730548369833660421810818427894647:ℚ)/13291850000000000000000000000000000000000000000000000000),((-7640111284436306496893:ℚ)/18050000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6597358661:ℚ)/10000000000),((3398653717:ℚ)/5000000000),((61541510627:ℚ)/116300000000),((4398653717:ℚ)/7150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5194879207:ℚ)/10000000000),((-537069145050148771395672575028480123442411326374503859209:ℚ)/7373614439062500000000000000000000000000000000000000000000),((-30632538220564110030653:ℚ)/72200000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6716974887:ℚ)/10000000000),((432305631:ℚ)/625000000),((20792941403:ℚ)/39400000000),((557305631:ℚ)/908593750),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((973693439:ℚ)/2000000000),((-20861241011836465280795931787351358014779678699167272849:ℚ)/286701487500000000000000000000000000000000000000000000000),((-1439148042126896541041:ℚ)/3384375000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((683656297:ℚ)/1000000000),((109944471:ℚ)/156250000),((6321594079:ℚ)/12010000000),((141194471:ℚ)/230859375),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4520632149:ℚ)/10000000000),((-2359679401817436783100661717832560146730867741477697677:ℚ)/32481067518750000000000000000000000000000000000000000000),((-360566110006703070359:ℚ)/846093750000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((6956124263:ℚ)/10000000000),((7155976837:ℚ)/10000000000),((64052869841:ℚ)/122000000000),((9155976837:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1036487681:ℚ)/2500000000),((-822729183117160972082491296065310732954234566418957236081:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-123327961525740438259613:ℚ)/288800000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1415132007:ℚ)/2000000000),((7394966813:ℚ)/10000000000),((763407297:ℚ)/1480000000),((9394966813:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((3736317607:ℚ)/10000000000),((-338629078166103618754726516919386468599516585747913:ℚ)/5065300000000000000000000000000000000000000000000000),((-122888460246760406774413:ℚ)/288800000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7314659699:ℚ)/10000000000),((3816934319:ℚ)/5000000000),((66562617893:ℚ)/129600000000),((4816934319:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((54977881:ℚ)/200000000),((-33550213794632822142887817674912010430302865057952572439:ℚ)/503884800000000000000000000000000000000000000000000000000),((-812638454392309:ℚ)/1900000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((3776785317:ℚ)/5000000000),((9542670327:ℚ)/10000000000),((34117497219:ℚ)/80000000000),((11542670327:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1105925633:ℚ)/10000000000),((-275313507537976108498974518982143537:ℚ)/24000000000000000000000000000000000000),((-412338707658947:ℚ)/950000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((473121471:ℚ)/500000000),((6676486769:ℚ)/5000000000),((1359950099:ℚ)/3680000000),((7676486769:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((285096567811435545538391:ℚ)/6771200000000000000000000),((-3482177:ℚ)/8000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC24
#check @N11Formalization.C450Source26GroupedC24.bound
#print axioms N11Formalization.C450Source26GroupedC24.valid0
#print axioms N11Formalization.C450Source26GroupedC24.valid1
#print axioms N11Formalization.C450Source26GroupedC24.valid2
#print axioms N11Formalization.C450Source26GroupedC24.valid3
#print axioms N11Formalization.C450Source26GroupedC24.valid4
#print axioms N11Formalization.C450Source26GroupedC24.valid5
#print axioms N11Formalization.C450Source26GroupedC24.valid6
#print axioms N11Formalization.C450Source26GroupedC24.valid7
#print axioms N11Formalization.C450Source26GroupedC24.valid8
#print axioms N11Formalization.C450Source26GroupedC24.valid9
#print axioms N11Formalization.C450Source26GroupedC24.valid10
#print axioms N11Formalization.C450Source26GroupedC24.valid11
#print axioms N11Formalization.C450Source26GroupedC24.bound
#print axioms N11Formalization.C450Source26GroupedC24.endpoint_checks
