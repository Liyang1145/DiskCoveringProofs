import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((636567437:ℚ)/1000000000),((6672582387:ℚ)/10000000000),((-3728582387:ℚ)/19840000000),((-252567437:ℚ)/2575000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2889709801:ℚ)/5000000000),((713822247358676287808736021837706809079015224361697673:ℚ)/3308060253906250000000000000000000000000000000000000000),((-42916525790117635307443:ℚ)/462080000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((132111421:ℚ)/200000000),((6792519857:ℚ)/10000000000),((-3848519857:ℚ)/20600000000),((-55311421:ℚ)/524500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5173070891:ℚ)/10000000000),((4918907179212891689484698683625864798135918946184457:ℚ)/23221684931054687500000000000000000000000000000000000),((-1956613731560614769427:ℚ)/18483200000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((1345090667:ℚ)/2000000000),((6912414463:ℚ)/10000000000),((-3968414463:ℚ)/20980000000),((-577090667:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4844567843:ℚ)/10000000000),((17582928319587737991081322416615655267982174471202830339:ℚ)/83195154112500000000000000000000000000000000000000000000),((-207729140583008505797683:ℚ)/1848320000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((855661847:ℚ)/1250000000),((439516781:ℚ)/625000000),((-255516781:ℚ)/1335000000),((-375661847:ℚ)/3396875000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2247129347:ℚ)/5000000000),((4598553263088254113957833387758811361538866128397648877:ℚ)/21802621796989440917968750000000000000000000000000000000),((-85876527828280417593623:ℚ)/722000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((435318597:ℚ)/625000000),((886522621:ℚ)/1250000000),((-518522621:ℚ)/2717500000),((-65106199:ℚ)/571093750),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4116541617:ℚ)/10000000000),((33095420656958145680270563309906208226217450193410449:ℚ)/158176439820602536201477050781250000000000000000000000),((-67970465198279541714119:ℚ)/541500000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((175624627:ℚ)/250000000),((7152084083:ℚ)/10000000000),((-4208084083:ℚ)/21930000000),((-79624627:ℚ)/691250000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3914936969:ℚ)/10000000000),((4929605797617088857802868449968354172099398443514067:ℚ)/23578862683677673339843750000000000000000000000000000),((-3720383838484647858463:ℚ)/28880000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7084863691:ℚ)/10000000000),((1442395617:ℚ)/2000000000),((-121942231:ℚ)/632000000),((-33452203:ℚ)/287500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3702997579:ℚ)/10000000000),((153205463298256067285756693112929438820177348097127:ℚ)/733332061767578125000000000000000000000000000000000),((-6105378205355135729582707:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((446545851:ℚ)/625000000),((908982901:ℚ)/1250000000),((-540982901:ℚ)/2788750000),((-22949539:ℚ)/195312500),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3478829813:ℚ)/10000000000),((84724272630066845445498603702680570526036024696219:ℚ)/405816535931080579757690429687500000000000000000000),((-73341082073517384326891:ℚ)/541500000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((180114877:ℚ)/250000000),((7391607719:ℚ)/10000000000),((-4447607719:ℚ)/22500000000),((-7646807:ℚ)/65000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((202493177:ℚ)/625000000),((1080815991078830293223387727542090049552193873639:ℚ)/5149218750000000000000000000000000000000000000000),((-4007373109103873875463:ℚ)/28880000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7324293479:ℚ)/10000000000),((7630999679:ℚ)/10000000000),((-4686999679:ℚ)/22880000000),((-3484293479:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((270180161:ℚ)/1000000000),((135856766398250747560627355879361744401273445592439029363:ℚ)/640598636132812500000000000000000000000000000000000000000),((-6719406093151574822796827:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7563597767:ℚ)/10000000000),((1574054491:ℚ)/2000000000),((-985254491:ℚ)/4728000000),((-3723597767:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3059819:ℚ)/31250000),((7391009079806497718882844940562319143062719196113218787641:ℚ)/34933794531250000000000000000000000000000000000000000000000),((-20327445807462900938403:ℚ)/128000000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((3901394227:ℚ)/5000000000),((8348502969:ℚ)/10000000000),((-5404502969:ℚ)/24400000000),((-1981394227:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((38838095928673123997830460392640906770341210619803849397:ℚ)/180099450000000000000000000000000000000000000000000000000),((-20589431:ℚ)/128000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((2070217379:ℚ)/2500000000),((2564583299:ℚ)/2500000000),((-1828583299:ℚ)/6480000000),((-1110217379:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((40235035343928251946781128524574148900766041332324370003:ℚ)/168750000000000000000000000000000000000000000000000000000),((-20589431:ℚ)/128000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((5095122989:ℚ)/5000000000),((14069836603:ℚ)/10000000000),((-11125836603:ℚ)/32000000000),((-3175122989:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8927336063144914958401677317991215141344346401972886639:ℚ)/32850900000000000000000000000000000000000000000000000000),((-20589431:ℚ)/128000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source25 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source25 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC12
#check @N11Formalization.C450Source25GroupedC12.bound
#print axioms N11Formalization.C450Source25GroupedC12.valid0
#print axioms N11Formalization.C450Source25GroupedC12.valid1
#print axioms N11Formalization.C450Source25GroupedC12.valid2
#print axioms N11Formalization.C450Source25GroupedC12.valid3
#print axioms N11Formalization.C450Source25GroupedC12.valid4
#print axioms N11Formalization.C450Source25GroupedC12.valid5
#print axioms N11Formalization.C450Source25GroupedC12.valid6
#print axioms N11Formalization.C450Source25GroupedC12.valid7
#print axioms N11Formalization.C450Source25GroupedC12.valid8
#print axioms N11Formalization.C450Source25GroupedC12.valid9
#print axioms N11Formalization.C450Source25GroupedC12.valid10
#print axioms N11Formalization.C450Source25GroupedC12.valid11
#print axioms N11Formalization.C450Source25GroupedC12.valid12
#print axioms N11Formalization.C450Source25GroupedC12.valid13
#print axioms N11Formalization.C450Source25GroupedC12.bound
#print axioms N11Formalization.C450Source25GroupedC12.endpoint_checks
