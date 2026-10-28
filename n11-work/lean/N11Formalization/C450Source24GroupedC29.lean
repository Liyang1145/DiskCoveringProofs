import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((2714629681:ℚ)/5000000000),((5989573297:ℚ)/10000000000),((9903889043:ℚ)/13350000000),((92584452861:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7750640273:ℚ)/10000000000),((-13136749067176344341037541893154977161:ℚ)/59481759375000000000000000000000000000),((-3235108716283590265015117:ℚ)/9241600000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((2952959381:ℚ)/5000000000),((6227950079:ℚ)/10000000000),((10618878143:ℚ)/13825000000),((95683351027:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((34038003:ℚ)/50000000),((-879529678887459360714650319528553938518943707449964303:ℚ)/3538902978515625000000000000000000000000000000000000000),((-3181431080116074827938733:ℚ)/9241600000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((6144162533:ℚ)/10000000000),((317355807:ℚ)/500000000),((21952487599:ℚ)/28125000000),((4861625491:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((786619209:ℚ)/1250000000),((-6061597616144110081874021173536415350754053010247071577:ℚ)/23174285888671875000000000000000000000000000000000000000),((-7885812898913917607637:ℚ)/23104000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((1565816373:ℚ)/2500000000),((6466268311:ℚ)/10000000000),((507040829:ℚ)/650000000),((32927162681:ℚ)/37500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((301080161:ℚ)/500000000),((-224172326237037325098302492578525455766362842627561:ℚ)/858203125000000000000000000000000000000000000000000),((-3127041032369521269390973:ℚ)/9241600000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1595589169:ℚ)/2500000000),((6525839403:ℚ)/10000000000),((5666767507:ℚ)/7209375000),((99555912239:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1434778733:ℚ)/2500000000),((-234842314565834967361243462988273722838478685058221789:ℚ)/878221638894081115722656250000000000000000000000000000),((-3113332111482903043635717:ℚ)/9241600000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1288379607:ℚ)/2000000000),((1646351819:ℚ)/2500000000),((4569138821:ℚ)/5815000000),((25082573647:ℚ)/28837500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((5593161541:ℚ)/10000000000),((-6566532369198579365031430866991548002541820032207081:ℚ)/24578714796875000000000000000000000000000000000000000),((-193723662735257675968493:ℚ)/577600000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((1300287333:ℚ)/2000000000),((6644972009:ℚ)/10000000000),((4604861999:ℚ)/5862500000),((101104636117:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5443729579:ℚ)/10000000000),((-18007328063368198984943744323392010981616440028064959:ℚ)/67462403869628906250000000000000000000000000000000000),((-3085780498231066434030653:ℚ)/9241600000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6560972633:ℚ)/10000000000),((6704533677:ℚ)/10000000000),((23202917899:ℚ)/29550000000),((101878937801:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((330657569:ℚ)/625000000),((-199114262205988538893961930095825835732190351953138573:ℚ)/746618457031250000000000000000000000000000000000000000),((-3071937784591958210218677:ℚ)/9241600000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6620506003:ℚ)/10000000000),((1352818471:ℚ)/2000000000),((23381518009:ℚ)/29787500000),((20530640123:ℚ)/23640000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((320824671:ℚ)/625000000),((-66023525350353390900731584822311106896728446642530411847:ℚ)/247784104376220703125000000000000000000000000000000000000),((-122322018093056171229533:ℚ)/369664000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3340018419:ℚ)/5000000000),((3411824057:ℚ)/5000000000),((11780055257:ℚ)/15012500000),((51713712741:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((4971356229:ℚ)/10000000000),((-175930539573889150105491678241561358438507830884456093:ℚ)/660829010391235351562500000000000000000000000000000000),((-761029622905667162766637:ℚ)/2310400000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((3369782599:ℚ)/5000000000),((6883201023:ℚ)/10000000000),((11869347797:ℚ)/15131250000),((104201613299:ℚ)/120100000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((4804546259:ℚ)/10000000000),((-319974962083874221721761490364169644693886130500350217:ℚ)/1202906668853759765625000000000000000000000000000000000),((-3030141892922771083919277:ℚ)/9241600000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((6799091141:ℚ)/10000000000),((6942751149:ℚ)/10000000000),((23917273423:ℚ)/30500000000),((104975764937:ℚ)/121050000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1158056079:ℚ)/2500000000),((-23565161353175976675130114408580808676661586166340556587:ℚ)/88664453125000000000000000000000000000000000000000000000),((-3016120646930120184876213:ℚ)/9241600000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((274344589:ℚ)/400000000),((706184331:ℚ)/1000000000),((963833767:ℚ)/1239000000),((10652396303:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((890749417:ℚ)/2000000000),((-18366127667699433156211976490974632028293790187343:ℚ)/70759483593750000000000000000000000000000000000000),((-29879441772329238187893:ℚ)/92416000000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((872206879:ℚ)/1250000000),((7180925091:ℚ)/10000000000),((3056620637:ℚ)/3931250000),((108072026183:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4075049833:ℚ)/10000000000),((-48067791195912083121370292923271169092797059726997:ℚ)/185413799434900283813476562500000000000000000000000),((-2959589014153829657159253:ℚ)/9241600000000000000000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((7096686539:ℚ)/10000000000),((3709529677:ℚ)/5000000000),((24810059617:ℚ)/32400000000),((55583885801:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1829885439:ℚ)/5000000000),((-975546195165743714832630066779215772320511995511885951:ℚ)/3936600000000000000000000000000000000000000000000000000),((-725585587987543010460677:ℚ)/2310400000000000000000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7334724707:ℚ)/10000000000),((932304563:ℚ)/1000000000),((25524174121:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1324945491:ℚ)/5000000000),((-5122624034877120969491269356411294246479248575522245527:ℚ)/37500000000000000000000000000000000000000000000000000000),((-39589481:ℚ)/128000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((9238107453:ℚ)/10000000000),((1640964897:ℚ)/1250000000),((31234322359:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1473749018267504497450818501199023233:ℚ)/21024576000000000000000000000000000000),((-39589481:ℚ)/128000000)⟩
theorem valid16 : Valid source24 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC29
#check @N11Formalization.C450Source24GroupedC29.bound
#print axioms N11Formalization.C450Source24GroupedC29.valid0
#print axioms N11Formalization.C450Source24GroupedC29.valid1
#print axioms N11Formalization.C450Source24GroupedC29.valid2
#print axioms N11Formalization.C450Source24GroupedC29.valid3
#print axioms N11Formalization.C450Source24GroupedC29.valid4
#print axioms N11Formalization.C450Source24GroupedC29.valid5
#print axioms N11Formalization.C450Source24GroupedC29.valid6
#print axioms N11Formalization.C450Source24GroupedC29.valid7
#print axioms N11Formalization.C450Source24GroupedC29.valid8
#print axioms N11Formalization.C450Source24GroupedC29.valid9
#print axioms N11Formalization.C450Source24GroupedC29.valid10
#print axioms N11Formalization.C450Source24GroupedC29.valid11
#print axioms N11Formalization.C450Source24GroupedC29.valid12
#print axioms N11Formalization.C450Source24GroupedC29.valid13
#print axioms N11Formalization.C450Source24GroupedC29.valid14
#print axioms N11Formalization.C450Source24GroupedC29.valid15
#print axioms N11Formalization.C450Source24GroupedC29.valid16
#print axioms N11Formalization.C450Source24GroupedC29.bound
#print axioms N11Formalization.C450Source24GroupedC29.endpoint_checks
