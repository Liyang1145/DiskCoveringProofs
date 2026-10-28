import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((5451648929:ℚ)/10000000000),((93885749:ℚ)/156250000),((83671436077:ℚ)/106800000000),((762200243:ℚ)/775000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1927112327:ℚ)/2500000000),((-1339589633318614182110138788112630596163:ℚ)/7613665200000000000000000000000000000000),((-624167906467474518636377:ℚ)/1805000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((5927600841:ℚ)/10000000000),((624674969:ℚ)/1000000000),((89858810933:ℚ)/110600000000),((5044724783:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3381072171:ℚ)/5000000000),((-2531763821353596134183554920325573711797227840171121732553:ℚ)/12683428275000000000000000000000000000000000000000000000000),((-25122088997682890738681297:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((1541381901:ℚ)/2500000000),((6365766287:ℚ)/10000000000),((23237964713:ℚ)/28125000000),((7325766287:ℚ)/7900000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6245033091:ℚ)/10000000000),((-4885444371350064075933294874816106969006875388655695813:ℚ)/23174285888671875000000000000000000000000000000000000000),((-2489946307716048727646722113:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6284480147:ℚ)/10000000000),((3242387:ℚ)/5000000),((94498241911:ℚ)/114400000000),((26056709:ℚ)/28125000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5972143937:ℚ)/10000000000),((-89562649270147174415869779477945713707007653661648960867:ℚ)/425339200000000000000000000000000000000000000000000000000),((-616909041430737779913:ℚ)/1848320000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((800428243:ℚ)/1250000000),((3301886633:ℚ)/5000000000),((12005567159:ℚ)/14537500000),((26473206431:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5687849283:ℚ)/10000000000),((-1514576444590026957607232917307014389574213349626719691:ℚ)/7200795350646972656250000000000000000000000000000000000),((-1693406095993820300102473:ℚ)/5120000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((652236533:ℚ)/1000000000),((3361382247:ℚ)/5000000000),((9759074929:ℚ)/11820000000),((26889675729:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((215612799:ℚ)/400000000),((-813238139781510149668343254205833168833322644840586589:ℚ)/3870470081250000000000000000000000000000000000000000000),((-1817154713829774762851832179:ℚ)/5544960000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((1660324653:ℚ)/2500000000),((1356451443:ℚ)/2000000000),((24784220489:ℚ)/29787500000),((3613053367:ℚ)/3940000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2538602077:ℚ)/5000000000),((-53332640555613626504440405159050498260040133952639586541:ℚ)/247784104376220703125000000000000000000000000000000000000),((-289398278842366979756686619:ℚ)/887193600000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((418797691:ℚ)/625000000),((6841748067:ℚ)/10000000000),((6244369983:ℚ)/7506250000),((54612236469:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((4913867937:ℚ)/10000000000),((-17766443737826501677387180093814492807932165091815401:ℚ)/82603626298904418945312500000000000000000000000000000),((-7201259252436389439288312059:ℚ)/22179840000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3380113041:ℚ)/5000000000),((862654637:ℚ)/1250000000),((50341469533:ℚ)/60525000000),((6878582459:ℚ)/7506250000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2372695311:ℚ)/5000000000),((-16546377959480847310504686932801916552723211072958042779:ℚ)/76986026806640625000000000000000000000000000000000000000),((-37330862900150672935267913:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((1704921931:ℚ)/2500000000),((870090543:ℚ)/1250000000),((25363985103:ℚ)/30500000000),((2310211267:ℚ)/2521875000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1142800103:ℚ)/2500000000),((-19043110809752789458617469805909570198893555373189148681:ℚ)/88664453125000000000000000000000000000000000000000000000),((-111464940996448711129577219:ℚ)/346560000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6879148013:ℚ)/10000000000),((3539846831:ℚ)/5000000000),((102228924169:ℚ)/123900000000),((28138927817:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2195306967:ℚ)/5000000000),((-11530726063913391916132344088321852037655094148302971221:ℚ)/55035153906250000000000000000000000000000000000000000000),((-588842467053670723403114497:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6998064659:ℚ)/10000000000),((7198656337:ℚ)/10000000000),((103774840567:ℚ)/125800000000),((8158656337:ℚ)/8850000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2003374301:ℚ)/5000000000),((-1271851781559608630094955064479970519861985101073053401:ℚ)/6075639379882812500000000000000000000000000000000000000),((-2332773080224300523504704513:ℚ)/7393280000000000000000000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((7116976261:ℚ)/10000000000),((7436562931:ℚ)/10000000000),((35106897131:ℚ)/43200000000),((58775940517:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1792214077:ℚ)/5000000000),((-1863423751745804410459775619537008836417297765649513311:ℚ)/9331200000000000000000000000000000000000000000000000000),((-6336386615870134909942177:ℚ)/20480000000000000000000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((7354785223:ℚ)/10000000000),((104849693:ℚ)/125000000),((108412207899:ℚ)/144800000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((2547159867:ℚ)/10000000000),((-90728049186029763373339350335068783852974064775712042613:ℚ)/592974100000000000000000000000000000000000000000000000000),((-156244851:ℚ)/512000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((103823233:ℚ)/125000000),((9339119083:ℚ)/10000000000),((1509702029:ℚ)/2000000000),((72093833581:ℚ)/72400000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-984884499488734451763408962263693702095130759300923:ℚ)/6250000000000000000000000000000000000000000000000000),((-156244851:ℚ)/512000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((4628363913:ℚ)/5000000000),((3285529329:ℚ)/2500000000),((66568730869:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-9094828646509716159285735939212375689:ℚ)/168196608000000000000000000000000000000),((-156244851:ℚ)/512000000)⟩
theorem valid15 : Valid source22 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source22 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC30
#check @N11Formalization.C450Source22GroupedC30.bound
#print axioms N11Formalization.C450Source22GroupedC30.valid0
#print axioms N11Formalization.C450Source22GroupedC30.valid1
#print axioms N11Formalization.C450Source22GroupedC30.valid2
#print axioms N11Formalization.C450Source22GroupedC30.valid3
#print axioms N11Formalization.C450Source22GroupedC30.valid4
#print axioms N11Formalization.C450Source22GroupedC30.valid5
#print axioms N11Formalization.C450Source22GroupedC30.valid6
#print axioms N11Formalization.C450Source22GroupedC30.valid7
#print axioms N11Formalization.C450Source22GroupedC30.valid8
#print axioms N11Formalization.C450Source22GroupedC30.valid9
#print axioms N11Formalization.C450Source22GroupedC30.valid10
#print axioms N11Formalization.C450Source22GroupedC30.valid11
#print axioms N11Formalization.C450Source22GroupedC30.valid12
#print axioms N11Formalization.C450Source22GroupedC30.valid13
#print axioms N11Formalization.C450Source22GroupedC30.valid14
#print axioms N11Formalization.C450Source22GroupedC30.valid15
#print axioms N11Formalization.C450Source22GroupedC30.bound
#print axioms N11Formalization.C450Source22GroupedC30.endpoint_checks
