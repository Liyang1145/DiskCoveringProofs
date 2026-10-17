import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((6231711691:ℚ)/10000000000),((6553733061:ℚ)/10000000000),((-14877393:ℚ)/3200000000),((3688288309:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1523628959:ℚ)/2500000000),((8673527622742871500882397567343:ℚ)/1638400000000000000000000000000000),((-113560227654637646283362043:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6473847301:ℚ)/10000000000),((1334923383:ℚ)/2000000000),((-164770149:ℚ)/20600000000),((3446152699:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1102685127:ℚ)/2000000000),((316791239702388070246434177401399545484235803155137:ℚ)/42684648437500000000000000000000000000000000000000000),((-125379517601159429174349403:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((1318957127:ℚ)/2000000000),((6795432369:ℚ)/10000000000),((-1186297107:ℚ)/104900000000),((665042873:ℚ)/10490000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((5201694883:ℚ)/10000000000),((13761711319045269511386101898506217714556792402963426719:ℚ)/1442900811250000000000000000000000000000000000000000000000),((-5253015532517941403674787:ℚ)/36966400000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((6715644021:ℚ)/10000000000),((6855812081:ℚ)/10000000000),((-455812081:ℚ)/35600000000),((3204355979:ℚ)/53400000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1218052223:ℚ)/2500000000),((1769699567085725255802119449954363800667809525764683151:ℚ)/169192560000000000000000000000000000000000000000000000000),((-411886931416192820645734769:ℚ)/2772480000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6776044601:ℚ)/10000000000),((6916173791:ℚ)/10000000000),((-1548521373:ℚ)/107750000000),((3143955399:ℚ)/53875000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4699635047:ℚ)/10000000000),((17903630292886119259092677866023163449208860655456357761:ℚ)/1563730292968750000000000000000000000000000000000000000000),((-140289966161742195382903203:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((1709106699:ℚ)/2500000000),((6976517983:ℚ)/10000000000),((-1729553949:ℚ)/108700000000),((770893301:ℚ)/13587500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((565130289:ℚ)/1250000000),((1245990614282213360082981012518606501660043479284240737:ℚ)/100341054921875000000000000000000000000000000000000000000),((-26866958188224887568876209:ℚ)/173280000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((68967911:ℚ)/100000000),((3518422561:ℚ)/5000000000),((-318422561:ℚ)/18275000000),((10077363:ℚ)/182750000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2167840701:ℚ)/5000000000),((2371319585150130702043326135943327876690524878924759:ℚ)/177424550781250000000000000000000000000000000000000000),((-14629709451217173299363:ℚ)/92416000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6957137989:ℚ)/10000000000),((286298001:ℚ)/400000000),((-1150557:ℚ)/56000000),((2962862011:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((258914887:ℚ)/625000000),((9820155319095104854097892159167158889889303:ℚ)/640000000000000000000000000000000000000000000),((-149309936200397051963199963:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7077781343:ℚ)/10000000000),((909748989:ℚ)/1250000000),((-109748989:ℚ)/4687500000),((315802073:ℚ)/6250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((932165751:ℚ)/2500000000),((2204262564961049026625515318115897087196901607064097:ℚ)/128746032714843750000000000000000000000000000000000000),((-155354259125625892586955347:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3599180173:ℚ)/5000000000),((7518899147:ℚ)/10000000000),((-3356697441:ℚ)/114400000000),((1360819827:ℚ)/28600000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1632780903:ℚ)/5000000000),((9751563806079799299888469161240111224659426733521958757:ℚ)/467873120000000000000000000000000000000000000000000000000),((-40355885209965250032802187:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7439338077:ℚ)/10000000000),((7759589829:ℚ)/10000000000),((-1359589829:ℚ)/39400000000),((2480661923:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1029918221:ℚ)/5000000000),((5501945671100938685462390841269817254361910650416011099:ℚ)/229361190000000000000000000000000000000000000000000000000),((-520912352559097250206538561:ℚ)/2772480000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7680094681:ℚ)/10000000000),((4120199809:ℚ)/5000000000),((-2760599427:ℚ)/61000000000),((2239905319:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2173283634776155887902167310911809044170357337950601751:ℚ)/70931562500000000000000000000000000000000000000000000000),((-3148253:ℚ)/16000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((2040256073:ℚ)/2500000000),((5079022821:ℚ)/5000000000),((-1879022821:ℚ)/21600000000),((146581309:ℚ)/5400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((133298220771413970724315922570026573597083221435132699:ℚ)/2361960000000000000000000000000000000000000000000000000),((-3148253:ℚ)/16000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((5039436019:ℚ)/5000000000),((559145733:ℚ)/400000000),((-909437199:ℚ)/6400000000),((-26478673:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((662037132473868843841555716645398529:ℚ)/6933708800000000000000000000000000000),((-3148253:ℚ)/16000000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC14
#check @N11Formalization.C450Source32GroupedC14.bound
#print axioms N11Formalization.C450Source32GroupedC14.valid0
#print axioms N11Formalization.C450Source32GroupedC14.valid1
#print axioms N11Formalization.C450Source32GroupedC14.valid2
#print axioms N11Formalization.C450Source32GroupedC14.valid3
#print axioms N11Formalization.C450Source32GroupedC14.valid4
#print axioms N11Formalization.C450Source32GroupedC14.valid5
#print axioms N11Formalization.C450Source32GroupedC14.valid6
#print axioms N11Formalization.C450Source32GroupedC14.valid7
#print axioms N11Formalization.C450Source32GroupedC14.valid8
#print axioms N11Formalization.C450Source32GroupedC14.valid9
#print axioms N11Formalization.C450Source32GroupedC14.valid10
#print axioms N11Formalization.C450Source32GroupedC14.valid11
#print axioms N11Formalization.C450Source32GroupedC14.valid12
#print axioms N11Formalization.C450Source32GroupedC14.valid13
#print axioms N11Formalization.C450Source32GroupedC14.bound
#print axioms N11Formalization.C450Source32GroupedC14.endpoint_checks
