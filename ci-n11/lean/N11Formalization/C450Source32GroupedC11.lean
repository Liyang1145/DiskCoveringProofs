import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6469310869:ℚ)/10000000000),((3339155219:ℚ)/5000000000),((-5217465657:ℚ)/24800000000),((-2501310869:ℚ)/20220000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5524809969:ℚ)/10000000000),((36079109611071030788460747546257506492549:ℚ)/259840057267200000000000000000000000000000),((53668377558723957255968237:ℚ)/1478656000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6590080573:ℚ)/10000000000),((3399518759:ℚ)/5000000000),((-1799518759:ℚ)/8425000000),((-2622080573:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((5214137171:ℚ)/10000000000),((69428047208112261004460458386682787661011065782232732867:ℚ)/495648970430908203125000000000000000000000000000000000000),((42785468690473779162116093:ℚ)/1478656000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1677693481:ℚ)/2500000000),((1714843323:ℚ)/2500000000),((-2744529969:ℚ)/12875000000),((-62335771:ℚ)/472500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1221469647:ℚ)/2500000000),((17258150155206128989036987640868426947770525387532707919:ℚ)/124083522691726684570312500000000000000000000000000000000),((1988069141702443277225637:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3385546659:ℚ)/5000000000),((6919691247:ℚ)/10000000000),((-3719691247:ℚ)/17325000000),((-1401546659:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4714000939:ℚ)/10000000000),((88274768373104919194339043610083121498940351933661430909:ℚ)/631935363339843750000000000000000000000000000000000000000),((19714361615921486419867831:ℚ)/1108992000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1707848801:ℚ)/2500000000),((3489995939:ℚ)/5000000000),((-5669987817:ℚ)/26225000000),((-715848801:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4536173547:ℚ)/10000000000),((194171630272896142878381355166559127139611662800552711192997:ℚ)/1384125148516738281250000000000000000000000000000000000000000),((3590561961518737822797:ℚ)/256000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((1722920017:ℚ)/2500000000),((3520137831:ℚ)/5000000000),((-5760413493:ℚ)/26462500000),((-730920017:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((870332317:ℚ)/2000000000),((222815860546526636709413158575344001960621461893111161381:ℚ)/1581701950401000976562500000000000000000000000000000000000),((948055892210415586119413:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((3475974189:ℚ)/5000000000),((3550271529:ℚ)/5000000000),((-1950271529:ℚ)/8900000000),((-1491974189:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2079784989:ℚ)/5000000000),((69463169337313403646068720268962453436458531599716328624519:ℚ)/491084049033750000000000000000000000000000000000000000000000),((7181413731546085378245271:ℚ)/1108992000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1402440117:ℚ)/2000000000),((1790198627:ℚ)/2500000000),((-2970595881:ℚ)/13468750000),((-608840117:ℚ)/4348000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((494848717:ℚ)/1250000000),((512501298220896526771094039979563802892373562291566917895757:ℚ)/3608701637759361267089843750000000000000000000000000000000000),((474964375142863196821639:ℚ)/177438720000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1768109281:ℚ)/2500000000),((7221030439:ℚ)/10000000000),((-12063091317:ℚ)/54350000000),((-776109281:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((936979689:ℚ)/2500000000),((955613094880572330578876421138663879439026964894833100157409:ℚ)/6702293306138505859375000000000000000000000000000000000000000),((-105167003426881595501163:ℚ)/92416000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7132658413:ℚ)/10000000000),((7281251263:ℚ)/10000000000),((-4081251263:ℚ)/18275000000),((-452094059:ℚ)/3160000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((705028083:ℚ)/2000000000),((158493739555632647522495410019534369153487082979559381353:ℚ)/1107306621425781250000000000000000000000000000000000000000),((-7346927141278306298769827:ℚ)/1478656000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((3596432429:ℚ)/5000000000),((3700824581:ℚ)/5000000000),((-6302473743:ℚ)/27650000000),((-1612432429:ℚ)/11250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3288028721:ℚ)/10000000000),((2120799907647348837080055077365243596155076326577671633:ℚ)/14560057968750000000000000000000000000000000000000000000),((-3258687067205416046208803:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((1828308689:ℚ)/2500000000),((7521991217:ℚ)/10000000000),((-1440663739:ℚ)/6250000000),((-836308689:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2755792927:ℚ)/10000000000),((915429532475803021109330038371284882527813731553837639303:ℚ)/6240539550781250000000000000000000000000000000000000000000),((-1530072618094514920671243:ℚ)/92416000000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((3716774889:ℚ)/5000000000),((1000356809:ℚ)/1250000000),((-138543879:ℚ)/550000000),((-1732774889:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1048373981:ℚ)/5000000000),((30756232799124569741178741979052052509730447700890123:ℚ)/193462929687500000000000000000000000000000000000000000),((-74838062878552618458089:ℚ)/3072000000000000000000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((7914313627:ℚ)/10000000000),((8483018773:ℚ)/10000000000),((-15849056319:ℚ)/61000000000),((-3946313627:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((25125648380897251493954140305561756201689644637399046305401:ℚ)/155127327187500000000000000000000000000000000000000000000000),((-3611681:ℚ)/102400000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((52464941:ℚ)/62500000),((2079742309:ℚ)/2000000000),((-479914103:ℚ)/1440000000),((-27664941:ℚ)/200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((141722355358820531316929956184124598179706581489793:ℚ)/699840000000000000000000000000000000000000000000000),((-3611681:ℚ)/102400000)⟩
theorem valid14 : Valid source32 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((5154909409:ℚ)/5000000000),((355426019:ℚ)/250000000),((-826278057:ℚ)/2000000000),((-1056969803:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((54247433307748701300130400859299703:ℚ)/211600000000000000000000000000000000),((-3611681:ℚ)/102400000)⟩
theorem valid15 : Valid source32 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC11
#check @N11Formalization.C450Source32GroupedC11.bound
#print axioms N11Formalization.C450Source32GroupedC11.valid0
#print axioms N11Formalization.C450Source32GroupedC11.valid1
#print axioms N11Formalization.C450Source32GroupedC11.valid2
#print axioms N11Formalization.C450Source32GroupedC11.valid3
#print axioms N11Formalization.C450Source32GroupedC11.valid4
#print axioms N11Formalization.C450Source32GroupedC11.valid5
#print axioms N11Formalization.C450Source32GroupedC11.valid6
#print axioms N11Formalization.C450Source32GroupedC11.valid7
#print axioms N11Formalization.C450Source32GroupedC11.valid8
#print axioms N11Formalization.C450Source32GroupedC11.valid9
#print axioms N11Formalization.C450Source32GroupedC11.valid10
#print axioms N11Formalization.C450Source32GroupedC11.valid11
#print axioms N11Formalization.C450Source32GroupedC11.valid12
#print axioms N11Formalization.C450Source32GroupedC11.valid13
#print axioms N11Formalization.C450Source32GroupedC11.valid14
#print axioms N11Formalization.C450Source32GroupedC11.valid15
#print axioms N11Formalization.C450Source32GroupedC11.bound
#print axioms N11Formalization.C450Source32GroupedC11.endpoint_checks
