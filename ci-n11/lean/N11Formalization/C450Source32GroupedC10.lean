import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1637346303:ℚ)/2500000000),((6762090649:ℚ)/10000000000),((-28134634543:ℚ)/99200000000),((-2432038909:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((16627037:ℚ)/31250000),((3052387141401992537259240573136296722101651:ℚ)/16629763665100800000000000000000000000000000),((5849912899976829693354303:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6670056393:ℚ)/10000000000),((3441349073:ℚ)/5000000000),((-14489443511:ℚ)/50550000000),((-10090169179:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1249705673:ℚ)/2500000000),((19737104700123021721187388872734198875226823575351620343763:ℚ)/107060177613076171875000000000000000000000000000000000000000),((86826778229363376171387183:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6790655031:ℚ)/10000000000),((1388595169:ℚ)/2000000000),((-5880166183:ℚ)/20600000000),((-10451965093:ℚ)/51975000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2328502337:ℚ)/5000000000),((11237472323503648861329613026186295420492824314462970929057:ℚ)/61497779182382812500000000000000000000000000000000000000000),((79988838559193617756906287:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6850928427:ℚ)/10000000000),((7003236827:ℚ)/10000000000),((-29822657789:ℚ)/103950000000),((-10632785281:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2238583041:ℚ)/5000000000),((24999731554984676541697702311426857589195225399967377368927:ℚ)/136498038481406250000000000000000000000000000000000000000000),((76545043124368740647539143:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1727796297:ℚ)/2500000000),((3531740777:ℚ)/5000000000),((-15122185439:ℚ)/52450000000),((-2703388891:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4290377277:ℚ)/10000000000),((2032653228748959994977524125414954187869725838707160993726611:ℚ)/11073001188133906250000000000000000000000000000000000000000000),((4567792508858101238789103:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6971425773:ℚ)/10000000000),((890463809:ℚ)/1250000000),((-3833246663:ℚ)/13231250000),((-10994277319:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((20478409:ℚ)/50000000),((54563571657362187801522767075065915496508526846511149339:ℚ)/296569115700187683105468750000000000000000000000000000000),((69607737558714844054683543:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((3515825313:ℚ)/5000000000),((7183924013:ℚ)/10000000000),((-31087468091:ℚ)/106800000000),((-5587475939:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3891887389:ℚ)/10000000000),((156475320403479995548758714737160485826615251020247255796550141:ℚ)/848593236730320000000000000000000000000000000000000000000000000),((16528550914413789107689023:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((7091860177:ℚ)/10000000000),((7244122591:ℚ)/10000000000),((-31508858137:ℚ)/107750000000),((-11355580531:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3677475601:ℚ)/10000000000),((341450439173145386198304764342812563060188733819106252208792181:ℚ)/1847655238532792968750000000000000000000000000000000000000000000),((62604067019466777544898143:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1788013709:ℚ)/2500000000),((1826076651:ℚ)/2500000000),((-7982536557:ℚ)/27175000000),((-2884041127:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3450461413:ℚ)/10000000000),((155164435270526157734149693800580053409180966120241724956649:ℚ)/837786663267313232421875000000000000000000000000000000000000),((3692332306044756626517527:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7212235003:ℚ)/10000000000),((7364476439:ℚ)/10000000000),((-32351335073:ℚ)/109650000000),((-11716705009:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((641632799:ℚ)/2000000000),((2175306723899378698890374292858010757589045311715813376855367:ℚ)/11719733281170468750000000000000000000000000000000000000000000),((55533942652718082310761703:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7272401059:ℚ)/10000000000),((935596881:ℚ)/1250000000),((-4149178167:ℚ)/13825000000),((-11897203177:ℚ)/56250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((589361749:ℚ)/2000000000),((342545362204838299943490677182873715539642448305807897:ℚ)/1820007246093750000000000000000000000000000000000000000),((51973934310172467525219127:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((7392692311:ℚ)/10000000000),((7605021241:ℚ)/10000000000),((-34035148687:ℚ)/112500000000),((-12258076933:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2341035939:ℚ)/10000000000),((6877101956205002909351017066178874590354282649911484341444611:ℚ)/36394826660156250000000000000000000000000000000000000000000000),((124110737531319928004887:ℚ)/2560000000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((37564657:ℚ)/50000000),((4282693203:ℚ)/5000000000),((-20378852421:ℚ)/57200000000),((-63093971:ℚ)/324000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((757572989:ℚ)/5000000000),((9315298225257253409978517906178334725465394881030856390473:ℚ)/42634938060000000000000000000000000000000000000000000000000),((939184214905159699583:ℚ)/23104000000000000000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((847324747:ℚ)/1000000000),((5240070441:ℚ)/5000000000),((-9026831029:ℚ)/21600000000),((-1549974241:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((584278490230878133438870643961375223023099252413934251:ℚ)/2361960000000000000000000000000000000000000000000000000),((1117853:ℚ)/32000000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((5193966189:ℚ)/5000000000),((3574344841:ℚ)/2500000000),((-20220413887:ℚ)/40000000000),((-10621898567:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((153105375257334718225071629:ℚ)/507840000000000000000000000),((1117853:ℚ)/32000000)⟩
theorem valid14 : Valid source32 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source32 nn0 nn1 Qcell ((2079:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((45:ℚ)/64) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC10
#check @N11Formalization.C450Source32GroupedC10.bound
#print axioms N11Formalization.C450Source32GroupedC10.valid0
#print axioms N11Formalization.C450Source32GroupedC10.valid1
#print axioms N11Formalization.C450Source32GroupedC10.valid2
#print axioms N11Formalization.C450Source32GroupedC10.valid3
#print axioms N11Formalization.C450Source32GroupedC10.valid4
#print axioms N11Formalization.C450Source32GroupedC10.valid5
#print axioms N11Formalization.C450Source32GroupedC10.valid6
#print axioms N11Formalization.C450Source32GroupedC10.valid7
#print axioms N11Formalization.C450Source32GroupedC10.valid8
#print axioms N11Formalization.C450Source32GroupedC10.valid9
#print axioms N11Formalization.C450Source32GroupedC10.valid10
#print axioms N11Formalization.C450Source32GroupedC10.valid11
#print axioms N11Formalization.C450Source32GroupedC10.valid12
#print axioms N11Formalization.C450Source32GroupedC10.valid13
#print axioms N11Formalization.C450Source32GroupedC10.valid14
#print axioms N11Formalization.C450Source32GroupedC10.bound
#print axioms N11Formalization.C450Source32GroupedC10.endpoint_checks
