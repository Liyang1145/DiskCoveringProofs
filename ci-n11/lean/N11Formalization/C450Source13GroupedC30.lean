import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((1443910907:ℚ)/2500000000),((6312569811:ℚ)/10000000000),((20530841791:ℚ)/26700000000),((48027988677:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((884444197:ℚ)/1250000000),((-22895680829913762879247805647611180443:ℚ)/475854075000000000000000000000000000000),((-111874966138019679017385911:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6250953827:ℚ)/10000000000),((3275119661:ℚ)/5000000000),((88302399751:ℚ)/110600000000),((24845837627:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((60501437:ℚ)/100000000),((-278209901037401775342464095059572125354746907770792213533:ℚ)/5073371310000000000000000000000000000000000000000000000000),((-76963409835039999662751:ℚ)/320000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((3244296463:ℚ)/5000000000),((169697439:ℚ)/250000000),((45695854019:ℚ)/57200000000),((1283882073:ℚ)/1382500000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((219050977:ℚ)/400000000),((-12859366514457924668311900583754146162662146564003586331:ℚ)/233936560000000000000000000000000000000000000000000000000),((-68997079849637828838911:ℚ)/288800000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((840777847:ℚ)/1250000000),((6906722797:ℚ)/10000000000),((11810112011:ℚ)/14537500000),((52187059579:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4842393543:ℚ)/10000000000),((-167088268329386976613380360012601086904952935460373793:ℚ)/2880318140258789062500000000000000000000000000000000000),((-110025396026221915202545719:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((6845034517:ℚ)/10000000000),((6966134501:ℚ)/10000000000),((96025448721:ℚ)/117250000000),((52602941507:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2247523431:ℚ)/5000000000),((-4281394673163579144908214247053796108754871425244168687:ℚ)/71959897460937500000000000000000000000000000000000000000),((-109840426557762060185928391:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1726109909:ℚ)/2500000000),((3512772807:ℚ)/5000000000),((24199428817:ℚ)/29550000000),((26509409649:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((269478991:ℚ)/625000000),((-53289679901370980577957689447327075075992154591401033:ℚ)/895942148437500000000000000000000000000000000000000000),((-27413863657530101066517359:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6963844271:ℚ)/10000000000),((7084956151:ℚ)/10000000000),((97569975523:ℚ)/119150000000),((53434693057:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1030165253:ℚ)/2500000000),((-377179943075888443688629976620044866821124843302080964241:ℚ)/6343273072031250000000000000000000000000000000000000000000),((-303242327414743138295031:ℚ)/1280000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((7023248433:ℚ)/10000000000),((57154929:ℚ)/80000000),((98342229629:ℚ)/120100000000),((430804503:ℚ)/476600000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1960460609:ℚ)/5000000000),((-8045069784660107056869081430314169819022032905764855829:ℚ)/135337781328125000000000000000000000000000000000000000000),((-6994272205901814820031:ℚ)/29573120000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7082652133:ℚ)/10000000000),((7203775549:ℚ)/10000000000),((33038159243:ℚ)/40350000000),((54266428843:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1855515063:ℚ)/5000000000),((-542235470946628457120836566011074912425152812707869483:ℚ)/9124269843750000000000000000000000000000000000000000000),((-109100523651245581616896791:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((3571027691:ℚ)/5000000000),((7263184437:ℚ)/10000000000),((49943359983:ℚ)/61000000000),((18227430353:ℚ)/20175000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3489152189:ℚ)/10000000000),((-16856668369818250295419377228912512007048135837108443727:ℚ)/283726250000000000000000000000000000000000000000000000000),((-108915541455338361984755879:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7201458191:ℚ)/10000000000),((7322592801:ℚ)/10000000000),((100658956483:ℚ)/122950000000),((55098149607:ℚ)/61000000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((1626415561:ℚ)/5000000000),((-34497972492193634903208355220652883729296881691942843267:ℚ)/580812053867187500000000000000000000000000000000000000000),((-108730556592244700371408991:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((726086057:ℚ)/1000000000),((7382000653:ℚ)/10000000000),((1449016963:ℚ)/1770000000),((55514004571:ℚ)/61475000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((299864949:ℚ)/1000000000),((-137200427129387636559959934334543670334922827651089:ℚ)/2310513750000000000000000000000000000000000000000000),((-108545569024711625212316919:ℚ)/462080000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((7320262529:ℚ)/10000000000),((3750407433:ℚ)/5000000000),((102203412877:ℚ)/125800000000),((9390950677:ℚ)/10325000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2721602629:ℚ)/10000000000),((-140932185667655482094130757215394931587105294982472637:ℚ)/2430255751953125000000000000000000000000000000000000000),((-27043896409160022845461199:ℚ)/115520000000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((297562609:ℚ)/400000000),((7738437641:ℚ)/10000000000),((1383304639:ℚ)/1728000000),((58009063487:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1030795513:ℚ)/5000000000),((-13231056482628265776057147788542023394142988477293:ℚ)/238878720000000000000000000000000000000000000000000),((-3734997:ℚ)/16000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((3838332989:ℚ)/5000000000),((4819604887:ℚ)/5000000000),((53418328857:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-1189852544937045271681253587443710981365660173133134537:ℚ)/40000000000000000000000000000000000000000000000000000000),((-3734997:ℚ)/16000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((9577299633:ℚ)/10000000000),((2688023193:ℚ)/2000000000),((131544895229:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-8286027446696869973788577968081592183:ℚ)/538229145600000000000000000000000000000),((-3734997:ℚ)/16000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC30
#check @N11Formalization.C450Source13GroupedC30.bound
#print axioms N11Formalization.C450Source13GroupedC30.valid0
#print axioms N11Formalization.C450Source13GroupedC30.valid1
#print axioms N11Formalization.C450Source13GroupedC30.valid2
#print axioms N11Formalization.C450Source13GroupedC30.valid3
#print axioms N11Formalization.C450Source13GroupedC30.valid4
#print axioms N11Formalization.C450Source13GroupedC30.valid5
#print axioms N11Formalization.C450Source13GroupedC30.valid6
#print axioms N11Formalization.C450Source13GroupedC30.valid7
#print axioms N11Formalization.C450Source13GroupedC30.valid8
#print axioms N11Formalization.C450Source13GroupedC30.valid9
#print axioms N11Formalization.C450Source13GroupedC30.valid10
#print axioms N11Formalization.C450Source13GroupedC30.valid11
#print axioms N11Formalization.C450Source13GroupedC30.valid12
#print axioms N11Formalization.C450Source13GroupedC30.valid13
#print axioms N11Formalization.C450Source13GroupedC30.valid14
#print axioms N11Formalization.C450Source13GroupedC30.valid15
#print axioms N11Formalization.C450Source13GroupedC30.bound
#print axioms N11Formalization.C450Source13GroupedC30.endpoint_checks
