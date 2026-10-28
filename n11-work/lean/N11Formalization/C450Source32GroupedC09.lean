import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((3315188363:ℚ)/5000000000),((6846829177:ℚ)/10000000000),((-4446829177:ℚ)/12400000000),((-4428772847:ℚ)/16850000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((510668451:ℚ)/1000000000),((2454452657301863279048958736385386899223:ℚ)/10826669052800000000000000000000000000000),((320942870251543586408601219:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((337546589:ℚ)/500000000),((6967299133:ℚ)/10000000000),((-4567299133:ℚ)/12637500000),((-1370826123:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4772085533:ℚ)/10000000000),((379894291184435344234087778704592516680334765422426804201:ℚ)/1672815275204315185546875000000000000000000000000000000000),((3078870513006121854217971:ℚ)/18483200000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6871418771:ℚ)/10000000000),((7027510031:ℚ)/10000000000),((-4627510031:ℚ)/12875000000),((-28259931397:ℚ)/103950000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4414477797:ℚ)/10000000000),((3376986662890543219841366610407813345537191257653528861801:ℚ)/15014106245698928833007812500000000000000000000000000000000),((1178755085828031590658049491:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6931637943:ℚ)/10000000000),((3543852737:ℚ)/5000000000),((-2343852737:ℚ)/6496875000),((-28681465601:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4225221017:ℚ)/10000000000),((3282735695566457055618976539175661325899333422685354123:ℚ)/14579563436429500579833984375000000000000000000000000000),((3456433860946446439148160097:ℚ)/22179840000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6991841503:ℚ)/10000000000),((111685717:ℚ)/156250000),((-148371434:ℚ)/409765625),((-1003547949:ℚ)/3650000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1006922627:ℚ)/2500000000),((181136510903568995350641803005797758384433836398203633:ℚ)/803617547769546508789062500000000000000000000000000000),((1125391443133317519555522459:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((1763007471:ℚ)/2500000000),((7208051687:ℚ)/10000000000),((-4808051687:ℚ)/13231250000),((-7381052297:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((764119467:ℚ)/2000000000),((133838590576012287645927930813069643761641235984303978497:ℚ)/593138231400375366210937500000000000000000000000000000000),((205967901867751086177354673:ℚ)/1386240000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((7112203501:ℚ)/10000000000),((7268203267:ℚ)/10000000000),((-4868203267:ℚ)/13350000000),((-29945424507:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3602286547:ℚ)/10000000000),((374392856517848274473764586115878710069262573399826608494373:ℚ)/1657408665488906250000000000000000000000000000000000000000000),((1071456646925022083911204051:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1793090689:ℚ)/2500000000),((7328341009:ℚ)/10000000000),((-4928341009:ℚ)/13468750000),((-7591634823:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1685286397:ℚ)/5000000000),((816065639644875836614578896460314340474408670686183657155133:ℚ)/3608701637759361267089843750000000000000000000000000000000000),((65267180118101747875767771:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3616254017:ℚ)/5000000000),((3724288223:ℚ)/5000000000),((-2524288223:ℚ)/6793750000),((-15393778119:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3122466929:ℚ)/10000000000),((5142089048966803715748032719057929796570376407290520260367:ℚ)/22474510008254642486572265625000000000000000000000000000000),((254237528278233346761883739:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((367637907:ℚ)/500000000),((7688896663:ℚ)/10000000000),((-5288896663:ℚ)/13825000000),((-1581465349:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((127886193:ℚ)/500000000),((24803836980666499230824809524227434116059781070623540807:ℚ)/106032274003906250000000000000000000000000000000000000000),((7214034739766152212178297:ℚ)/55449600000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((7593106179:ℚ)/10000000000),((216212481:ℚ)/250000000),((-156212481:ℚ)/357500000),((-33311743253:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((212981089:ℚ)/5000000000),((21706922308485829635851442683907452408722627590351329:ℚ)/83271363398437500000000000000000000000000000000000000),((2549984529548461517942677273:ℚ)/22179840000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((4276401623:ℚ)/5000000000),((10562172803:ℚ)/10000000000),((-8162172803:ℚ)/16200000000),((-20014811361:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((62371439010826120835553919852127393831:ℚ)/216000000000000000000000000000000000000),((58639249:ℚ)/512000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((5233305391:ℚ)/5000000000),((3594538487:ℚ)/2500000000),((-2994538487:ℚ)/5000000000),((-26713137737:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((699084287995223927141416109:ℚ)/2031360000000000000000000000),((58639249:ℚ)/512000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source32 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC09
#check @N11Formalization.C450Source32GroupedC09.bound
#print axioms N11Formalization.C450Source32GroupedC09.valid0
#print axioms N11Formalization.C450Source32GroupedC09.valid1
#print axioms N11Formalization.C450Source32GroupedC09.valid2
#print axioms N11Formalization.C450Source32GroupedC09.valid3
#print axioms N11Formalization.C450Source32GroupedC09.valid4
#print axioms N11Formalization.C450Source32GroupedC09.valid5
#print axioms N11Formalization.C450Source32GroupedC09.valid6
#print axioms N11Formalization.C450Source32GroupedC09.valid7
#print axioms N11Formalization.C450Source32GroupedC09.valid8
#print axioms N11Formalization.C450Source32GroupedC09.valid9
#print axioms N11Formalization.C450Source32GroupedC09.valid10
#print axioms N11Formalization.C450Source32GroupedC09.valid11
#print axioms N11Formalization.C450Source32GroupedC09.valid12
#print axioms N11Formalization.C450Source32GroupedC09.bound
#print axioms N11Formalization.C450Source32GroupedC09.endpoint_checks
