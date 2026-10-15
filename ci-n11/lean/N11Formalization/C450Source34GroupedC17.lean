import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(0:ℚ),((1:ℚ)/16),((1493979037:ℚ)/2500000000),((3154481189:ℚ)/5000000000),((512:ℚ)/2575),((442402619:ℚ)/1600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3329956109:ℚ)/5000000000),((-1717622340509235652319247909032250272039:ℚ)/10490179200000000000000000000000000000000),((-854986228978709201262119441:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((6218754833:ℚ)/10000000000),((803760829:ℚ)/1250000000),((1024:ℚ)/5245),((3443760829:ℚ)/12875000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((244969437:ℚ)/400000000),((-3838669479984818178191547779662967483807091:ℚ)/23918335478986328125000000000000000000000000),((-55541993335867257890859361:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((49531441:ℚ)/78125000),((409445247:ℚ)/625000000),((256:ℚ)/1335),((1729445247:ℚ)/6556250000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((116818181:ℚ)/200000000),((-16086975395369164415537605826297062381859:ℚ)/102271542965639648437500000000000000000000),((-42367546602244208580066667:ℚ)/173280000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((1292240329:ℚ)/2000000000),((1668019767:ℚ)/2500000000),((1024:ℚ)/5435),((2316006589:ℚ)/8900000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1109021631:ℚ)/2000000000),((-3923500998535049962115872933920977811369949:ℚ)/25433647873157500000000000000000000000000000),((-689203378019525047673145307:ℚ)/2772480000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((3291145733:ℚ)/5000000000),((6792956373:ℚ)/10000000000),((512:ℚ)/2765),((27912956373:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2617338019:ℚ)/5000000000),((-28358357894988312077514214942485157066335349:ℚ)/187329320793293437500000000000000000000000000),((-11207558260856835942585494227:ℚ)/44359680000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((6703298587:ℚ)/10000000000),((3456879973:ℚ)/5000000000),((1024:ℚ)/5625),((14016879973:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((196271709:ℚ)/400000000),((-15361081548201677065119461247634315079737:ℚ)/103343225097656250000000000000000000000000),((-948917757358008036221989009:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((6824227357:ℚ)/10000000000),((1758623397:ℚ)/2500000000),((128:ℚ)/715),((2346207799:ℚ)/9375000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2278824143:ℚ)/5000000000),((-3127649280399460192545176263784626319413:ℚ)/21417531738281250000000000000000000000000),((-722851653357335217951308467:ℚ)/2772480000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((3472540909:ℚ)/5000000000),((7275764997:ℚ)/10000000000),((512:ℚ)/2955),((28395764997:ℚ)/114400000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2090936897:ℚ)/5000000000),((-26873600192767949815802388566312878929401:ℚ)/190465257840000000000000000000000000000000),((-11700288252892410061531863667:ℚ)/44359680000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((7186582643:ℚ)/10000000000),((1503359239:ℚ)/2000000000),((256:ℚ)/1525),((5727359239:ℚ)/23640000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1656766049:ℚ)/5000000000),((-180601810371793133758591125668640333767263:ℚ)/1321335844350000000000000000000000000000000),((-160692988123686600872652841:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7427828303:ℚ)/10000000000),((3999112403:ℚ)/5000000000),((64:ℚ)/405),((14559112403:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1066307331:ℚ)/5000000000),((-21229786453019408132524577777432267376889:ℚ)/164790996750000000000000000000000000000000),((-273253639115028777:ℚ)/972800000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((7909646533:ℚ)/10000000000),((9917741681:ℚ)/10000000000),((16:ℚ)/125),((31037741681:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-31266954877043722896220203398764723289:ℚ)/291600000000000000000000000000000000000),((-58975367:ℚ)/204800000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9830340471:ℚ)/10000000000),((6870254727:ℚ)/5000000000),((32:ℚ)/345),((17430254727:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-65767698874349441183878145428830662720989:ℚ)/788421600000000000000000000000000000000000),((-58975367:ℚ)/204800000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC17
#check @N11Formalization.C450Source34GroupedC17.bound
#print axioms N11Formalization.C450Source34GroupedC17.valid0
#print axioms N11Formalization.C450Source34GroupedC17.valid1
#print axioms N11Formalization.C450Source34GroupedC17.valid2
#print axioms N11Formalization.C450Source34GroupedC17.valid3
#print axioms N11Formalization.C450Source34GroupedC17.valid4
#print axioms N11Formalization.C450Source34GroupedC17.valid5
#print axioms N11Formalization.C450Source34GroupedC17.valid6
#print axioms N11Formalization.C450Source34GroupedC17.valid7
#print axioms N11Formalization.C450Source34GroupedC17.valid8
#print axioms N11Formalization.C450Source34GroupedC17.valid9
#print axioms N11Formalization.C450Source34GroupedC17.valid10
#print axioms N11Formalization.C450Source34GroupedC17.valid11
#print axioms N11Formalization.C450Source34GroupedC17.bound
#print axioms N11Formalization.C450Source34GroupedC17.endpoint_checks
