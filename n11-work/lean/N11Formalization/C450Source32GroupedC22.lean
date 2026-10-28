import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/16),((3:ℚ)/8),((140687641:ℚ)/250000000),((5960773929:ℚ)/10000000000),((236687641:ℚ)/515000000),((27802321787:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7370399177:ℚ)/10000000000),((-1326175970036711752570513843966000949511209918983370431680613:ℚ)/4854569763840000000000000000000000000000000000000000000000000),((-337177446621566688615905647:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((5869037513:ℚ)/10000000000),((6201948383:ℚ)/10000000000),((9709037513:ℚ)/21360000000),((28525845149:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((860542713:ℚ)/1250000000),((-272981822536053910284913118449910149008400619600269124940931:ℚ)/1014315300820312500000000000000000000000000000000000000000000),((-336918140890514019291747263:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((6110275657:ℚ)/10000000000),((6322437129:ℚ)/10000000000),((9950275657:ℚ)/21740000000),((28887311387:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((63683201:ℚ)/100000000),((-3469905765982605215873643781397854803569268854786799309:ℚ)/12843655030000000000000000000000000000000000000000000000),((-340085981625983848903740847:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6230794503:ℚ)/10000000000),((6442864863:ℚ)/10000000000),((1438684929:ℚ)/3160000000),((29248594589:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3048311907:ℚ)/5000000000),((-165251766974922616397758606456983689307322881413133:ℚ)/616298750000000000000000000000000000000000000000000),((-339779000187343464208882623:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((3175625629:ℚ)/5000000000),((6563234761:ℚ)/10000000000),((5095625629:ℚ)/11250000000),((29609704283:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1453516579:ℚ)/2500000000),((-5552314230663768142802403990581578060591926301023251:ℚ)/20856857299804687500000000000000000000000000000000000),((-339402135075917240626153007:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((6471649157:ℚ)/10000000000),((6683549783:ℚ)/10000000000),((10311649157:ℚ)/22880000000),((29970649349:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2759472291:ℚ)/5000000000),((-3958331215503081602095539082721341187142734636224168009:ℚ)/14971939840000000000000000000000000000000000000000000000),((-338955482898374761722878063:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((1647997803:ℚ)/2500000000),((6803812687:ℚ)/10000000000),((2607997803:ℚ)/5815000000),((30331438061:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5209087841:ℚ)/10000000000),((-64555756169844016339345973849048740231352715665696679:ℚ)/245787147968750000000000000000000000000000000000000000),((-338439133681186598943493023:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((839035029:ℚ)/1250000000),((6924026051:ℚ)/10000000000),((439678343:ℚ)/985000000),((30692078153:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4881654347:ℚ)/10000000000),((-77947774786950852879192545853407013441288454458771:ℚ)/298647382812500000000000000000000000000000000000000),((-337853171293521734122786167:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((170812971:ℚ)/250000000),((223884801:ℚ)/312500000),((266812971:ℚ)/610000000),((981654403:ℚ)/1846875000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2266399287:ℚ)/5000000000),((-72487829743485999239231261819022559326530335512063:ℚ)/283726250000000000000000000000000000000000000000000),((-325274364355082931046167:ℚ)/902500000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((7072854467:ℚ)/10000000000),((1528878113:ℚ)/2000000000),((10912854467:ℚ)/25920000000),((6570634339:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3746418423:ℚ)/10000000000),((-1782701122329416355086960849842284745622871568954315213:ℚ)/7255941120000000000000000000000000000000000000000000000),((-42677305954159781:ℚ)/121600000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((472063673:ℚ)/625000000),((9559818823:ℚ)/10000000000),((712063673:ℚ)/2000000000),((38599456469:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((556242779:ℚ)/5000000000),((-6305625347031888077614261338035704908936201749420143:ℚ)/30000000000000000000000000000000000000000000000000000),((-2778764041704239:ℚ)/7600000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((473435577:ℚ)/500000000),((6688920309:ℚ)/5000000000),((221811859:ℚ)/736000000),((25026760927:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-67341142089932878472097291375408892388094689892821:ℚ)/373770240000000000000000000000000000000000000000000),((-23491933:ℚ)/64000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC22
#check @N11Formalization.C450Source32GroupedC22.bound
#print axioms N11Formalization.C450Source32GroupedC22.valid0
#print axioms N11Formalization.C450Source32GroupedC22.valid1
#print axioms N11Formalization.C450Source32GroupedC22.valid2
#print axioms N11Formalization.C450Source32GroupedC22.valid3
#print axioms N11Formalization.C450Source32GroupedC22.valid4
#print axioms N11Formalization.C450Source32GroupedC22.valid5
#print axioms N11Formalization.C450Source32GroupedC22.valid6
#print axioms N11Formalization.C450Source32GroupedC22.valid7
#print axioms N11Formalization.C450Source32GroupedC22.valid8
#print axioms N11Formalization.C450Source32GroupedC22.valid9
#print axioms N11Formalization.C450Source32GroupedC22.valid10
#print axioms N11Formalization.C450Source32GroupedC22.valid11
#print axioms N11Formalization.C450Source32GroupedC22.bound
#print axioms N11Formalization.C450Source32GroupedC22.endpoint_checks
