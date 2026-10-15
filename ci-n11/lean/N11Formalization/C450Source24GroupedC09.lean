import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((6534294673:ℚ)/10000000000),((54784039:ℚ)/80000000),((-40704039:ℚ)/99200000),((-31020062711:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5359662091:ℚ)/10000000000),((71084227096432725465146668057256511607181888031962402418407:ℚ)/317573784375000000000000000000000000000000000000000000000000),((65347484536523146411159053:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((846709991:ℚ)/1250000000),((6967658111:ℚ)/10000000000),((-5207658111:ℚ)/12875000000),((-4086969937:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1176625271:ℚ)/2500000000),((39507832680554222250277754481376894892445051899663435979:ℚ)/181419413523864746093750000000000000000000000000000000000),((930709095511861663999517:ℚ)/9241600000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6893320753:ℚ)/10000000000),((3513736217:ℚ)/5000000000),((-2633736217:ℚ)/6556250000),((-33533245271:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((869307561:ℚ)/2000000000),((835569635909210490433862610607435202334114130130670249673931:ℚ)/3887747913295703125000000000000000000000000000000000000000000),((56645068506171178265665613:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((3476564521:ℚ)/5000000000),((885909857:ℚ)/1250000000),((-665909857:ℚ)/1653906250),((-5658650549:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((129866363:ℚ)/312500000),((2003871304079430261935481314538451895613561938809317387717:ℚ)/9327621081250000000000000000000000000000000000000000000000),((13794395869967994069487037:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((3506464769:ℚ)/5000000000),((1786769397:ℚ)/2500000000),((-1346769397:ℚ)/3337500000),((-17185253383:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3956301701:ℚ)/10000000000),((109447215965621013924799255169083535328255005949626589121:ℚ)/509663071560859680175781250000000000000000000000000000000),((13426302145669620850298477:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7072722453:ℚ)/10000000000),((1801717209:ℚ)/2500000000),((-1361717209:ℚ)/3367187500),((-34789057171:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((374689307:ℚ)/1000000000),((371336784386428492600076696578208388864278158470137088898609:ℚ)/1729879786853125000000000000000000000000000000000000000000000),((156683821662443381970121039:ℚ)/1774387200000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7132507987:ℚ)/10000000000),((7266652797:ℚ)/10000000000),((-5506652797:ℚ)/13587500000),((-35207555909:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((220357103:ℚ)/625000000),((80078199461819522474392120118620408250788845766438555419629:ℚ)/373185041762988281250000000000000000000000000000000000000000),((50745776359554875269223733:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3596143167:ℚ)/5000000000),((7326429661:ℚ)/10000000000),((-5566429661:ℚ)/13706250000),((-17813002169:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3290385267:ℚ)/10000000000),((184969476932488420297257106073708619030978025721784637657:ℚ)/862312692431640625000000000000000000000000000000000000000),((102338046493417699048879:ℚ)/1228800000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7252057683:ℚ)/10000000000),((7386199611:ℚ)/10000000000),((-5626199611:ℚ)/13825000000),((-36044403781:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3037615599:ℚ)/10000000000),((32147801610307553513634781728718785950318121529358306670993:ℚ)/149921491509350585937500000000000000000000000000000000000000),((143300243152395905132565919:ℚ)/1774387200000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((3655911107:ℚ)/5000000000),((297838513:ℚ)/400000000),((-9888631:ℚ)/24250000),((-18231377749:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2762615193:ℚ)/10000000000),((135524146783339135767436164874799666251820531620322875171:ℚ)/632223486900329589843750000000000000000000000000000000000),((11567469410581889110212693:ℚ)/147865600000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((3685790051:ℚ)/5000000000),((7565469727:ℚ)/10000000000),((-5805469727:ℚ)/14062500000),((-18440530357:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2457926819:ℚ)/10000000000),((1140315834142026958159947416390396653299885525416811419113:ℚ)/5263572600000000000000000000000000000000000000000000000000),((11192025037871798869371157:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3745538311:ℚ)/5000000000),((3902204933:ℚ)/5000000000),((-274745903:ℚ)/650000000),((-6286256059:ℚ)/19700000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((847537297:ℚ)/5000000000),((1319909427882234620914967803514965620441775999639680551:ℚ)/5972947656250000000000000000000000000000000000000000000),((10437453158619947673675997:ℚ)/147865600000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7729997019:ℚ)/10000000000),((4021629763:ℚ)/5000000000),((-1047209921:ℚ)/2462500000),((-39389979133:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((739392145599938460039783881880715429354032867514017445414703:ℚ)/3353644275000000000000000000000000000000000000000000000000000),((67487727:ℚ)/1024000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((3984414093:ℚ)/5000000000),((8520719573:ℚ)/10000000000),((-6760719573:ℚ)/15250000000),((-20530898651:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3943452545759340705446921349391349634101790613502820677753:ℚ)/17289547200000000000000000000000000000000000000000000000000),((67487727:ℚ)/1024000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((1055781819:ℚ)/1250000000),((10428209471:ℚ)/10000000000),((-2889403157:ℚ)/5400000000),((-5550472733:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((180436269594108352210210773531444440160609898509554261411:ℚ)/675000000000000000000000000000000000000000000000000000000),((67487727:ℚ)/1024000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((5176821041:ℚ)/5000000000),((3559245201:ℚ)/2500000000),((-3119245201:ℚ)/5000000000),((-28877747287:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((973781632131128260293456655616421552251203276631259509281:ℚ)/3153686400000000000000000000000000000000000000000000000000),((67487727:ℚ)/1024000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC09
#check @N11Formalization.C450Source24GroupedC09.bound
#print axioms N11Formalization.C450Source24GroupedC09.valid0
#print axioms N11Formalization.C450Source24GroupedC09.valid1
#print axioms N11Formalization.C450Source24GroupedC09.valid2
#print axioms N11Formalization.C450Source24GroupedC09.valid3
#print axioms N11Formalization.C450Source24GroupedC09.valid4
#print axioms N11Formalization.C450Source24GroupedC09.valid5
#print axioms N11Formalization.C450Source24GroupedC09.valid6
#print axioms N11Formalization.C450Source24GroupedC09.valid7
#print axioms N11Formalization.C450Source24GroupedC09.valid8
#print axioms N11Formalization.C450Source24GroupedC09.valid9
#print axioms N11Formalization.C450Source24GroupedC09.valid10
#print axioms N11Formalization.C450Source24GroupedC09.valid11
#print axioms N11Formalization.C450Source24GroupedC09.valid12
#print axioms N11Formalization.C450Source24GroupedC09.valid13
#print axioms N11Formalization.C450Source24GroupedC09.valid14
#print axioms N11Formalization.C450Source24GroupedC09.valid15
#print axioms N11Formalization.C450Source24GroupedC09.bound
#print axioms N11Formalization.C450Source24GroupedC09.endpoint_checks
