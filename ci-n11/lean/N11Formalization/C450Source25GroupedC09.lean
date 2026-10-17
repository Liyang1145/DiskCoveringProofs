import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((3273529537:ℚ)/5000000000),((274543553:ℚ)/400000000),((-200943553:ℚ)/496000000),((-15234706759:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5326681913:ℚ)/10000000000),((6386178392954786469957364941390274927681030729061566857939:ℚ)/26464482031250000000000000000000000000000000000000000000000),((79338442230427204399776887:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6786621903:ℚ)/10000000000),((436457707:ℚ)/625000000),((-321457707:ℚ)/804687500),((-32146353321:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4668808567:ℚ)/10000000000),((43646884802581376194039085016509368109681060718497111741357:ℚ)/185773479448437500000000000000000000000000000000000000000000),((858295891768038608596788421:ℚ)/8871936000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((431646661:ℚ)/625000000),((352158857:ℚ)/500000000),((-260158857:ℚ)/655625000),((-2061526627:ℚ)/6615625000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4305656231:ℚ)/10000000000),((440330443226044520994176901923139228366906649093058668337:ℚ)/1898314410788917541503906250000000000000000000000000000000),((1055876366158292807162783:ℚ)/11552000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((6966195633:ℚ)/10000000000),((7103022349:ℚ)/10000000000),((-5263022349:ℚ)/13231250000),((-11134456477:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((82258583:ℚ)/200000000),((34607915852489526854780796351555305483202994385030872694451:ℚ)/149241937300000000000000000000000000000000000000000000000000),((787096377397206661240012741:ℚ)/8871936000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((7026036157:ℚ)/10000000000),((7162859169:ℚ)/10000000000),((-5322859169:ℚ)/13350000000),((-33822253099:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((977827721:ℚ)/2500000000),((630155524478578144303743647174879387615639709393795764601:ℚ)/2718203048324584960937500000000000000000000000000000000000),((254398709554265573983713327:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7085868377:ℚ)/10000000000),((451417989:ℚ)/625000000),((-336417989:ℚ)/841796875),((-34241078639:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((924835747:ℚ)/2500000000),((801862662446769161597046001741239607890918711339961630973299:ℚ)/3459759573706250000000000000000000000000000000000000000000000),((246404082749295739274367367:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3572846257:ℚ)/5000000000),((728250853:ℚ)/1000000000),((-544250853:ℚ)/1358750000),((-17329923799:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((695025381:ℚ)/2000000000),((7205960460957844870603083350196205802426091390178279931347:ℚ)/31098753480249023437500000000000000000000000000000000000000),((59595390273510149565925527:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3602754391:ℚ)/5000000000),((3671160747:ℚ)/5000000000),((-2751160747:ℚ)/6853125000),((-17539280737:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1618056121:ℚ)/5000000000),((2796680244541095510892982015600102085307250091644947703897:ℚ)/12072377694042968750000000000000000000000000000000000000000),((57582781869776598313573863:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((1453063477:ℚ)/2000000000),((58296289:ℚ)/78125000),((-87842578:ℚ)/216015625),((-7099444339:ℚ)/22500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((744683227:ℚ)/2500000000),((36015002844302834013060282467997862711534915822850210497:ℚ)/153784561157226562500000000000000000000000000000000000000),((8890110629287338907061567:ℚ)/118292480000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((738491239:ℚ)/1000000000),((1895374961:ℚ)/2500000000),((-1435374961:ℚ)/3515625000),((-3633438673:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((95390581:ℚ)/400000000),((6570150476510608523601531753048894157820113262398905041:ℚ)/28072387200000000000000000000000000000000000000000000000),((2060121941687286537925383:ℚ)/29573120000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((1500895807:ℚ)/2000000000),((1007442487:ℚ)/1250000000),((-777442487:ℚ)/1787500000),((-7434270649:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1587133563:ℚ)/10000000000),((3222392139095090372479943417910877479567913977247297575317:ℚ)/12983313200000000000000000000000000000000000000000000000000),((7586389058152428331883127:ℚ)/118292480000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((3991244433:ℚ)/5000000000),((8537220367:ℚ)/10000000000),((-6697220367:ℚ)/15250000000),((-6752903677:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((105294220880913320906033732901671504583347851750612978747:ℚ)/426902400000000000000000000000000000000000000000000000000),((61119353:ℚ)/1024000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((13218973:ℚ)/15625000),((2611345019:ℚ)/2500000000),((-2151345019:ℚ)/4050000000),((-68532811:ℚ)/250000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((763347565942231156209703187608913429548365353528587:ℚ)/2636718750000000000000000000000000000000000000000000),((61119353:ℚ)/1024000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10368221559:ℚ)/10000000000),((14254933759:ℚ)/10000000000),((-12414933759:ℚ)/20000000000),((-19072516971:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((208537951472645564074173821394906522476555506329276024041:ℚ)/622950400000000000000000000000000000000000000000000000000),((61119353:ℚ)/1024000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source25 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC09
#check @N11Formalization.C450Source25GroupedC09.bound
#print axioms N11Formalization.C450Source25GroupedC09.valid0
#print axioms N11Formalization.C450Source25GroupedC09.valid1
#print axioms N11Formalization.C450Source25GroupedC09.valid2
#print axioms N11Formalization.C450Source25GroupedC09.valid3
#print axioms N11Formalization.C450Source25GroupedC09.valid4
#print axioms N11Formalization.C450Source25GroupedC09.valid5
#print axioms N11Formalization.C450Source25GroupedC09.valid6
#print axioms N11Formalization.C450Source25GroupedC09.valid7
#print axioms N11Formalization.C450Source25GroupedC09.valid8
#print axioms N11Formalization.C450Source25GroupedC09.valid9
#print axioms N11Formalization.C450Source25GroupedC09.valid10
#print axioms N11Formalization.C450Source25GroupedC09.valid11
#print axioms N11Formalization.C450Source25GroupedC09.valid12
#print axioms N11Formalization.C450Source25GroupedC09.valid13
#print axioms N11Formalization.C450Source25GroupedC09.bound
#print axioms N11Formalization.C450Source25GroupedC09.endpoint_checks
