import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((9:ℚ)/16),((5:ℚ)/8),((2644386691:ℚ)/5000000000),((140747847:ℚ)/250000000),((34039480219:ℚ)/51500000000),((193547847:ℚ)/248000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((100142019:ℚ)/125000000),((-3481415786689780033750887540945333981549208354280873:ℚ)/9819113600000000000000000000000000000000000000000000),((-4263317284560576475110721:ℚ)/9241600000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5529496929:ℚ)/10000000000),((5870570919:ℚ)/10000000000),((70245472361:ℚ)/106800000000),((7982570919:ℚ)/10300000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7560298899:ℚ)/10000000000),((-161439394519275553476238011043147172004884825233102454581:ℚ)/455872045312500000000000000000000000000000000000000000000),((-6733998269190540043135822209:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((576998673:ℚ)/1000000000),((1497703771:ℚ)/2500000000),((7240988057:ℚ)/10870000000),((2025703771:ℚ)/2670000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3543498761:ℚ)/5000000000),((-15700388831686874222463812432594669533423534896107822863:ℚ)/43104448293750000000000000000000000000000000000000000000),((-419037271885957821167917929:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((235606073:ℚ)/400000000),((3055503487:ℚ)/5000000000),((2939654657:ℚ)/4424000000),((4111503487:ℚ)/5435000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1710124051:ℚ)/2500000000),((-1351379649646330821116497827733441214727725584547212043:ℚ)/3715754690075683593750000000000000000000000000000000000),((-87603439736976946229734219:ℚ)/194560000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((3005133729:ℚ)/5000000000),((62311493:ℚ)/100000000),((37286203561:ℚ)/56250000000),((83431493:ℚ)/110600000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((823301377:ℚ)/1250000000),((-107954654420973288126735321525959287672899412381:ℚ)/297267850195312500000000000000000000000000000000),((-660989862257258703571881:ℚ)/1478656000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((6130336191:ℚ)/10000000000),((6291202673:ℚ)/10000000000),((75653025719:ℚ)/113450000000),((8403202673:ℚ)/11250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((790474733:ℚ)/1250000000),((-18552427975245178753384897310506101816816179657136647189:ℚ)/50479156494140625000000000000000000000000000000000000000),((-6593494828102133720455967601:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6190353723:ℚ)/10000000000),((6351244589:ℚ)/10000000000),((76193183507:ℚ)/114400000000),((8463244589:ℚ)/11345000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1237789231:ℚ)/2000000000),((-479228239117767168307943798606794473798991363493877500259:ℚ)/1305057225458593750000000000000000000000000000000000000000),((-345723413943992013967234371:ℚ)/778240000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((1562590103:ℚ)/2500000000),((6411275337:ℚ)/10000000000),((19183310927:ℚ)/28837500000),((8523275337:ℚ)/11440000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6051516357:ℚ)/10000000000),((-309393341181847232888161292484569775684412680760400363:ℚ)/843268193625000000000000000000000000000000000000000000),((-6543688214975666210583953761:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6310356533:ℚ)/10000000000),((1617823799:ℚ)/2500000000),((77273208797:ℚ)/116300000000),((2145823799:ℚ)/2883750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1477831239:ℚ)/2500000000),((-21300864127505845785441051586454826914399421140663893207:ℚ)/58104704912145996093750000000000000000000000000000000000),((-21441858331646512103393851:ℚ)/48640000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((127406847:ℚ)/200000000),((6591303323:ℚ)/10000000000),((1556261623:ℚ)/2364000000),((8703303323:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1442041717:ℚ)/2500000000),((-525378543854041131287531788030511359580443324970092922989:ℚ)/1452602044495312500000000000000000000000000000000000000000),((-6458647861892045972272788201:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6490284083:ℚ)/10000000000),((6711271029:ℚ)/10000000000),((78892556747:ℚ)/120100000000),((2941090343:ℚ)/3940000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1367999783:ℚ)/2500000000),((-631385849898739209190692832678100461452779737966200521:ℚ)/1747860337500000000000000000000000000000000000000000000),((-337146224816250087473458291:ℚ)/778240000000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((3305093779:ℚ)/5000000000),((3415600119:ℚ)/5000000000),((39985844011:ℚ)/61000000000),((4471600119:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2580387401:ℚ)/5000000000),((-29786994984884021881986190588809128796124953975519216043:ℚ)/82556046610156250000000000000000000000000000000000000000),((-1587920750846545635735184609:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6730054597:ℚ)/10000000000),((3535475141:ℚ)/5000000000),((81050491373:ℚ)/125800000000),((4591475141:ℚ)/6100000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2415776053:ℚ)/5000000000),((-235532322115675754126643291247823100887116271144952736211:ℚ)/669239292187500000000000000000000000000000000000000000000),((-81891725884182134916517331:ℚ)/194560000000000000000000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((871210761:ℚ)/1250000000),((456910413:ℚ)/625000000),((10400896849:ℚ)/16200000000),((34641789:ℚ)/46250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((164057053:ℚ)/400000000),((-475956782295097298647591450695083136225881573489:ℚ)/1353625488281250000000000000000000000000000000000),((-23855527140242480288776761:ℚ)/57760000000000000000000000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((1802297749:ℚ)/2500000000),((4611921159:ℚ)/5000000000),((21340679741:ℚ)/40000000000),((1889307053:ℚ)/2160000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3220841201:ℚ)/10000000000),((-2888017021001469485568444228856379826231880658833447:ℚ)/11809800000000000000000000000000000000000000000000000),((-24476492404404931:ℚ)/60800000000000000)⟩
theorem valid14 : Valid source34 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((4560884787:ℚ)/5000000000),((13039360453:ℚ)/10000000000),((51287963083:ℚ)/110400000000),((15151360453:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-11196436902948276032652213165050796323:ℚ)/70656000000000000000000000000000000000),((-415859603:ℚ)/1024000000)⟩
theorem valid15 : Valid source34 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC26
#check @N11Formalization.C450Source34GroupedC26.bound
#print axioms N11Formalization.C450Source34GroupedC26.valid0
#print axioms N11Formalization.C450Source34GroupedC26.valid1
#print axioms N11Formalization.C450Source34GroupedC26.valid2
#print axioms N11Formalization.C450Source34GroupedC26.valid3
#print axioms N11Formalization.C450Source34GroupedC26.valid4
#print axioms N11Formalization.C450Source34GroupedC26.valid5
#print axioms N11Formalization.C450Source34GroupedC26.valid6
#print axioms N11Formalization.C450Source34GroupedC26.valid7
#print axioms N11Formalization.C450Source34GroupedC26.valid8
#print axioms N11Formalization.C450Source34GroupedC26.valid9
#print axioms N11Formalization.C450Source34GroupedC26.valid10
#print axioms N11Formalization.C450Source34GroupedC26.valid11
#print axioms N11Formalization.C450Source34GroupedC26.valid12
#print axioms N11Formalization.C450Source34GroupedC26.valid13
#print axioms N11Formalization.C450Source34GroupedC26.valid14
#print axioms N11Formalization.C450Source34GroupedC26.valid15
#print axioms N11Formalization.C450Source34GroupedC26.bound
#print axioms N11Formalization.C450Source34GroupedC26.endpoint_checks
