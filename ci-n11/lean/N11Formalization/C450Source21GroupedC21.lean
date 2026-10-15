import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((5903251171:ℚ)/10000000000),((644431421:ℚ)/1000000000),((8943251171:ℚ)/26700000000),((900431421:ℚ)/1984000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1362635109:ℚ)/2000000000),((8831040816484292993430892151009582537:ℚ)/139183429976064000000000000000000000000),((-9285194319588370114341589:ℚ)/29573120000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6381600483:ℚ)/10000000000),((6683220227:ℚ)/10000000000),((9421600483:ℚ)/27650000000),((3081073409:ℚ)/7120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2870473667:ℚ)/5000000000),((5595441014704151580649058033011413193808671685241332204697:ℚ)/98553538249600000000000000000000000000000000000000000000000),((-50877745396748563465698039:ℚ)/155648000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((6620600863:ℚ)/10000000000),((6922032061:ℚ)/10000000000),((9660600863:ℚ)/28600000000),((9482032061:ℚ)/22120000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((64161757:ℚ)/125000000),((846985045146671421097518456059377968091344938205704225769:ℚ)/15200786801200000000000000000000000000000000000000000000000),((-983509896746238208812375509:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6859500683:ℚ)/10000000000),((880175697:ℚ)/1250000000),((9899500683:ℚ)/29075000000),((1200175697:ℚ)/2860000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4451040317:ℚ)/10000000000),((2629513852344771486852958880929532240748703967304784718663:ℚ)/49439896722287500000000000000000000000000000000000000000000),((-46989066282263367918124583:ℚ)/138624000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6978915999:ℚ)/10000000000),((1790189723:ℚ)/2500000000),((10018915999:ℚ)/29550000000),((2430189723:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4070861367:ℚ)/10000000000),((1891239551544155109390648463682905558829250243028974283679:ℚ)/35770325345697070312500000000000000000000000000000000000000),((-63171792453942722175853541:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((887288719:ℚ)/1250000000),((3640046489:ℚ)/5000000000),((1267288719:ℚ)/3753125000),((4920046489:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((182689899:ℚ)/500000000),((783079202671511098972218361606624246385424640988942992461871:ℚ)/14887386441773550000000000000000000000000000000000000000000000),((-254756150127958435190878109:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((225552593:ℚ)/312500000),((7399408741:ℚ)/10000000000),((320552593:ℚ)/953125000),((9959408741:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3185353543:ℚ)/10000000000),((16878530500689735483120081415525473951387484335077428355939:ℚ)/322298805966050000000000000000000000000000000000000000000000),((-1027261269705506180219454949:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((7337036639:ℚ)/10000000000),((7637988649:ℚ)/10000000000),((10377036639:ℚ)/31450000000),((10197988649:ℚ)/24400000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1319125389:ℚ)/5000000000),((482472083759414035936002818526735903353399476148666679087631:ℚ)/8980298982100000000000000000000000000000000000000000000000000),((-21254683068959403:ℚ)/60800000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((1515137773:ℚ)/2000000000),((3938252411:ℚ)/5000000000),((235904197:ℚ)/720000000),((5218252411:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((400033777:ℚ)/5000000000),((53808964821273882165366118987417572913949181128618785141:ℚ)/1007875665450000000000000000000000000000000000000000000000),((-4337752422765921:ℚ)/12160000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((3907136529:ℚ)/5000000000),((39131553:ℚ)/40000000),((5427136529:ℚ)/20000000000),((49371553:ℚ)/103680000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((29913540995575643514106924800390109645491171607:ℚ)/435356467200000000000000000000000000000000000000),((-73205831:ℚ)/204800000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((2430270797:ℚ)/2500000000),((13590366471:ℚ)/10000000000),((1063423599:ℚ)/4600000000),((16150366471:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((966344060554165629984883:ℚ)/10580000000000000000000000),((-73205831:ℚ)/204800000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC21
#check @N11Formalization.C450Source21GroupedC21.bound
#print axioms N11Formalization.C450Source21GroupedC21.valid0
#print axioms N11Formalization.C450Source21GroupedC21.valid1
#print axioms N11Formalization.C450Source21GroupedC21.valid2
#print axioms N11Formalization.C450Source21GroupedC21.valid3
#print axioms N11Formalization.C450Source21GroupedC21.valid4
#print axioms N11Formalization.C450Source21GroupedC21.valid5
#print axioms N11Formalization.C450Source21GroupedC21.valid6
#print axioms N11Formalization.C450Source21GroupedC21.valid7
#print axioms N11Formalization.C450Source21GroupedC21.valid8
#print axioms N11Formalization.C450Source21GroupedC21.valid9
#print axioms N11Formalization.C450Source21GroupedC21.valid10
#print axioms N11Formalization.C450Source21GroupedC21.bound
#print axioms N11Formalization.C450Source21GroupedC21.endpoint_checks
