import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6137285347:ℚ)/10000000000),((1660705761:ℚ)/2500000000),((11897285347:ℚ)/106800000000),((2460705761:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6308311773:ℚ)/10000000000),((861356208385552606841480498692680053693:ℚ)/33980329584000000000000000000000000000000),((-525059184628235628102114593:ℚ)/7393280000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((33065959:ℚ)/50000000),((430040999:ℚ)/625000000),((61865959:ℚ)/553000000),((630040999:ℚ)/3337500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2576379329:ℚ)/5000000000),((5151088082105553563843457631522482117863135002939245931523:ℚ)/213164734602062988281250000000000000000000000000000000000000),((-13893279793066405923337:ℚ)/184832000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6851098189:ℚ)/10000000000),((3499782001:ℚ)/5000000000),((12611098189:ℚ)/112500000000),((5099782001:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4476650077:ℚ)/10000000000),((36215595900120081596063042778764394347013040209747621977:ℚ)/1528806086718750000000000000000000000000000000000000000000),((-571076513002762615720892417:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((6970041063:ℚ)/10000000000),((3529508011:ℚ)/5000000000),((12730041063:ℚ)/113450000000),((5129508011:ℚ)/28125000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4100254797:ℚ)/10000000000),((16805262413819746734336745493665881828947414257614963228603509:ℚ)/715857538032531738281250000000000000000000000000000000000000000),((-1736254773875839093127514139:ℚ)/22179840000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((878688759:ℚ)/1250000000),((7118466761:ℚ)/10000000000),((1598688759:ℚ)/14300000000),((10318466761:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1949651777:ℚ)/5000000000),((21846722741085382434490515586953073879629748664186391347111:ℚ)/933115916202894531250000000000000000000000000000000000000000),((-27308894273982560583412411:ℚ)/346560000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((1417795503:ℚ)/2000000000),((5742333:ℚ)/8000000),((856598501:ℚ)/7690000000),((638641:ℚ)/3520000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((368801147:ℚ)/1000000000),((2823299781446361078206550063421471229789218490213:ℚ)/120898789017600000000000000000000000000000000000000),((-70371397255028462371374379:ℚ)/887193600000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7148443433:ℚ)/10000000000),((180934113:ℚ)/250000000),((12908443433:ℚ)/116300000000),((260934113:ℚ)/1441875000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((692896561:ℚ)/2000000000),((7871030814870117800975611809893432020513407676180071601:ℚ)/337878859064128967285156250000000000000000000000000000000),((-590267291739225654766547753:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/16),((1:ℚ)/8),((3603953931:ℚ)/5000000000),((18242029:ℚ)/25000000),((926279133:ℚ)/8375000000),((26242029:ℚ)/145375000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((322617059:ℚ)/1000000000),((500835444297095893047334414588394106137650437427659:ℚ)/21549580219369506835937500000000000000000000000000000),((-445580017978957309347557491:ℚ)/5544960000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((3633685419:ℚ)/5000000000),((91953219:ℚ)/125000000),((2171228473:ℚ)/19700000000),((131953219:ℚ)/732812500),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((185594553:ℚ)/625000000),((2213512518039428162642926941727663347530748389387316871:ℚ)/95453328241848945617675781250000000000000000000000000000),((-1242271141502044808147131:ℚ)/15360000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7326832397:ℚ)/10000000000),((7475145987:ℚ)/10000000000),((13086832397:ℚ)/120100000000),((10675145987:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2689256829:ℚ)/10000000000),((129579319338947194935696911623509285679567313808788663148860479:ℚ)/5582769915665081250000000000000000000000000000000000000000000000),((-601786750439855544672644993:ℚ)/7393280000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((3722875699:ℚ)/5000000000),((3797015067:ℚ)/5000000000),((6602875699:ℚ)/61000000000),((5397015067:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((403632471:ℚ)/2000000000),((14553026174954865474638681602403523561013759869087651372453:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-152367126880321729096018177:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((60517321:ℚ)/80000000),((8069527329:ℚ)/10000000000),((106597321:ℚ)/1036800000),((11269527329:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((30145911:ℚ)/312500000),((54497144325022756834742292300893705291850933575157677763799:ℚ)/2326909907812500000000000000000000000000000000000000000000000),((-39497726617465907454057:ℚ)/473169920000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((4020135967:ℚ)/5000000000),((9971043231:ℚ)/10000000000),((6900135967:ℚ)/80000000000),((13171043231:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((7765755184669095505250271480283825466832759499267678387:ℚ)/318864600000000000000000000000000000000000000000000000000),((-8579439:ℚ)/102400000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((4971060947:ℚ)/5000000000),((137728219:ℚ)/100000000),((7851060947:ℚ)/110400000000),((169728219:ℚ)/800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((17041056903546897923208491764635223:ℚ)/609408000000000000000000000000000000),((-8579439:ℚ)/102400000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC18
#check @N11Formalization.C450Source11GroupedC18.bound
#print axioms N11Formalization.C450Source11GroupedC18.valid0
#print axioms N11Formalization.C450Source11GroupedC18.valid1
#print axioms N11Formalization.C450Source11GroupedC18.valid2
#print axioms N11Formalization.C450Source11GroupedC18.valid3
#print axioms N11Formalization.C450Source11GroupedC18.valid4
#print axioms N11Formalization.C450Source11GroupedC18.valid5
#print axioms N11Formalization.C450Source11GroupedC18.valid6
#print axioms N11Formalization.C450Source11GroupedC18.valid7
#print axioms N11Formalization.C450Source11GroupedC18.valid8
#print axioms N11Formalization.C450Source11GroupedC18.valid9
#print axioms N11Formalization.C450Source11GroupedC18.valid10
#print axioms N11Formalization.C450Source11GroupedC18.valid11
#print axioms N11Formalization.C450Source11GroupedC18.valid12
#print axioms N11Formalization.C450Source11GroupedC18.valid13
#print axioms N11Formalization.C450Source11GroupedC18.bound
#print axioms N11Formalization.C450Source11GroupedC18.endpoint_checks
