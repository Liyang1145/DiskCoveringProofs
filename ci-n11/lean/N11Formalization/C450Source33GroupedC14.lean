import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((778567729:ℚ)/1250000000),((6553723183:ℚ)/10000000000),((178830451:ℚ)/103000000000),((501432271:ℚ)/6200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6101798441:ℚ)/10000000000),((-20312117596489257698193107460155837457867717347760572071249:ℚ)/1968957463125000000000000000000000000000000000000000000000000),((-3403850616536169603548753:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((3235495453:ℚ)/5000000000),((3337313583:ℚ)/5000000000),((-91940749:ℚ)/51500000000),((1884504547:ℚ)/25750000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5520596311:ℚ)/10000000000),((-2606350695997185470197442106370445156781147124425843:ℚ)/333473815917968750000000000000000000000000000000000000),((-60369195401463824936188697:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((6592076961:ℚ)/10000000000),((6795521271:ℚ)/10000000000),((-546563813:ℚ)/104900000000),((3647923039:ℚ)/52450000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1302215281:ℚ)/2500000000),((-3891568170266240822641566505647546131899570766736040739:ℚ)/721450405625000000000000000000000000000000000000000000000),((-701844441958486963044713:ℚ)/5120000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((6713077519:ℚ)/10000000000),((3427983021:ℚ)/5000000000),((-363949063:ℚ)/53400000000),((1175640827:ℚ)/17800000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4879417101:ℚ)/10000000000),((-1223060754027465540745187669433987239189986070637032963:ℚ)/285512445000000000000000000000000000000000000000000000000),((-265304663470965708336104113:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6773547203:ℚ)/10000000000),((6916394169:ℚ)/10000000000),((-909182507:ℚ)/107750000000),((3466452797:ℚ)/53875000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1176721547:ℚ)/2500000000),((-2465609592497300365418486199934399083797733905693246141:ℚ)/781865146484375000000000000000000000000000000000000000000),((-271292839552913674775572697:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((683399723:ℚ)/1000000000),((6976803567:ℚ)/10000000000),((-1090410701:ℚ)/108700000000),((340600277:ℚ)/5435000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((452835449:ℚ)/1000000000),((-308334977550003646599606252926773383088899647457425521:ℚ)/150511582382812500000000000000000000000000000000000000000),((-2772935803053263636142857:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((689442813:ℚ)/1000000000),((439824671:ℚ)/625000000),((-79474013:ℚ)/6853125000),((334557187:ℚ)/5482500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4343076321:ℚ)/10000000000),((-4528619493171385886581222320786938907367096620737:ℚ)/4678186397552490234375000000000000000000000000000000),((-2833069243769934676706777:ℚ)/18483200000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6954840411:ℚ)/10000000000),((3578962149:ℚ)/5000000000),((-816886447:ℚ)/55300000000),((3285159589:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4150142367:ℚ)/10000000000),((18628317534819083961874813906399358392222823571771737:ℚ)/15099319375000000000000000000000000000000000000000000000),((-289332908732727027133383593:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((3537805537:ℚ)/5000000000),((1819646627:ℚ)/2500000000),((-498939881:ℚ)/28125000000),((1582194463:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3736494103:ℚ)/10000000000),((45263587561357644733370953290843371281823609912351113:ℚ)/13904571533203125000000000000000000000000000000000000000),((-75355735296909741403464977:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((899539119:ℚ)/1250000000),((7519722267:ℚ)/10000000000),((-209166677:ℚ)/8800000000),((380460881:ℚ)/7150000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3273949429:ℚ)/10000000000),((398414390014238312606555814925707656784218091248699447:ℚ)/53985360000000000000000000000000000000000000000000000000),((-4899436714597852499090513:ℚ)/28880000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((1859381011:ℚ)/2500000000),((7760626639:ℚ)/10000000000),((-3441879917:ℚ)/118200000000),((233539663:ℚ)/4925000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((207147413:ℚ)/1000000000),((33881040579225233942537632128318135920293134365705972063:ℚ)/3096376065000000000000000000000000000000000000000000000000),((-21124993319249774085219193:ℚ)/115520000000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((153569977:ℚ)/200000000),((4120912397:ℚ)/5000000000),((-2442737191:ℚ)/61000000000),((51230023:ℚ)/1220000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((647605872171424308657633132991875833782493470471509407:ℚ)/35465781250000000000000000000000000000000000000000000000),((-12278039:ℚ)/64000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((2039956249:ℚ)/2500000000),((10160645143:ℚ)/10000000000),((-10641935429:ℚ)/129600000000),((57782639:ℚ)/1800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((11781334364414302608544804932072787165138329255529596311:ℚ)/255091680000000000000000000000000000000000000000000000000),((-12278039:ℚ)/64000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((629939513:ℚ)/625000000),((13982605287:ℚ)/10000000000),((-22107815861:ℚ)/160000000000),((10060487:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((45442788952835772967644383309281745131:ℚ)/512000000000000000000000000000000000000),((-12278039:ℚ)/64000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC14
#check @N11Formalization.C450Source33GroupedC14.bound
#print axioms N11Formalization.C450Source33GroupedC14.valid0
#print axioms N11Formalization.C450Source33GroupedC14.valid1
#print axioms N11Formalization.C450Source33GroupedC14.valid2
#print axioms N11Formalization.C450Source33GroupedC14.valid3
#print axioms N11Formalization.C450Source33GroupedC14.valid4
#print axioms N11Formalization.C450Source33GroupedC14.valid5
#print axioms N11Formalization.C450Source33GroupedC14.valid6
#print axioms N11Formalization.C450Source33GroupedC14.valid7
#print axioms N11Formalization.C450Source33GroupedC14.valid8
#print axioms N11Formalization.C450Source33GroupedC14.valid9
#print axioms N11Formalization.C450Source33GroupedC14.valid10
#print axioms N11Formalization.C450Source33GroupedC14.valid11
#print axioms N11Formalization.C450Source33GroupedC14.valid12
#print axioms N11Formalization.C450Source33GroupedC14.valid13
#print axioms N11Formalization.C450Source33GroupedC14.bound
#print axioms N11Formalization.C450Source33GroupedC14.endpoint_checks
