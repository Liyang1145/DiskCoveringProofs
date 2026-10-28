import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1633111579:ℚ)/2500000000),((6739558877:ℚ)/10000000000),((-29256912139:ℚ)/99200000000),((-2579334737:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5364422631:ℚ)/10000000000),((523478736501359889982534784921586953760359:ℚ)/2682219945984000000000000000000000000000000),((5300118456463448777849:ℚ)/64000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6652864633:ℚ)/10000000000),((857491207:ℚ)/1250000000),((-3762438449:ℚ)/12637500000),((-10678593899:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((5045813881:ℚ)/10000000000),((181823826769253675992623220997206387273415967492070865011:ℚ)/929341819557952880859375000000000000000000000000000000000),((27965366082094120592071481:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3386610073:ℚ)/5000000000),((6920092381:ℚ)/10000000000),((-30520646667:ℚ)/103000000000),((-5519830219:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2353917513:ℚ)/5000000000),((7455501136137740863073716264836398369710986706802983294652891:ℚ)/38436111988989257812500000000000000000000000000000000000000000),((6323133705238747818130041:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((213542983:ℚ)/312500000),((6980240559:ℚ)/10000000000),((-4420240559:ℚ)/14850000000),((-350628949:ℚ)/1639062500),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((906044811:ℚ)/2000000000),((1636601383107699795082048120516707495373747988926104424277:ℚ)/8425804844531250000000000000000000000000000000000000000000),((23385585690705034615881:ℚ)/361000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6893516357:ℚ)/10000000000),((7040374591:ℚ)/10000000000),((-31362622137:ℚ)/104900000000),((-11400549071:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2172963283:ℚ)/5000000000),((86148895027969296839573384410724369928362742872091579255106059:ℚ)/442920047525356250000000000000000000000000000000000000000000000),((22594952350099413110167521:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6953643249:ℚ)/10000000000),((443780929:ℚ)/625000000),((-1986466503:ℚ)/6615625000),((-11580929747:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4154047387:ℚ)/10000000000),((5583657821353153844485789806137750121469180210091513076669:ℚ)/28668347851018142700195312500000000000000000000000000000000),((21236868254892137336103529:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((3506878257:ℚ)/5000000000),((895075219:ℚ)/1250000000),((-4025526533:ℚ)/13350000000),((-5880634771:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3953477303:ℚ)/10000000000),((59860837953634544837952172882502473216247640838740428659687:ℚ)/306927530646093750000000000000000000000000000000000000000000),((4968145830574173298258921:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((7073856521:ℚ)/10000000000),((3610347807:ℚ)/5000000000),((-16312434649:ℚ)/53875000000),((-11941569563:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((748562747:ℚ)/2000000000),((225526676976287076704209724969904122877730022307892931139419051:ℚ)/1154784524082995605468750000000000000000000000000000000000000000),((18502093543654185283859289:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7133943627:ℚ)/10000000000),((1820194199:ℚ)/2500000000),((-8261359393:ℚ)/27175000000),((-12121830881:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1760119581:ℚ)/5000000000),((819199665496134646265182318822600859808897849473884326546587:ℚ)/4188933316336566162109375000000000000000000000000000000000000),((17125395025170745949874241:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((287760727:ℚ)/400000000),((7340845633:ℚ)/10000000000),((-11155306477:ℚ)/36550000000),((-492082181:ℚ)/2212000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1641662981:ℚ)/5000000000),((25000585177065714044400075103493792619946326115986780750013:ℚ)/127665939882031250000000000000000000000000000000000000000000),((25187974465030215922841:ℚ)/591462400000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((1450816099:ℚ)/2000000000),((7460947551:ℚ)/10000000000),((-4900947551:ℚ)/15800000000),((-2496448297:ℚ)/11250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((15143523:ℚ)/50000000),((131840823633708321170690445915819268973719743447855044047:ℚ)/665602650000000000000000000000000000000000000000000000000),((574134280637356967955729:ℚ)/14786560000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((3687084861:ℚ)/5000000000),((379050191:ℚ)/500000000),((-585783779:ℚ)/1875000000),((-6421254583:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2443884053:ℚ)/10000000000),((18587765446029704704289292607294381924556182800411448249:ℚ)/93608093261718750000000000000000000000000000000000000000),((2889110244493794542729809:ℚ)/92416000000000000000000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((1498842747:ℚ)/2000000000),((8060815913:ℚ)/10000000000),((-38505711391:ℚ)/114400000000),((-2640528241:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((417607123:ℚ)/2500000000),((1831429551689037575414484998086379171919512300431810109567789:ℚ)/8704779397600000000000000000000000000000000000000000000000000),((349384820361872643569761:ℚ)/14786560000000000000000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((124593449:ℚ)/156250000),((341602241:ℚ)/400000000),((-1674415687:ℚ)/4880000000),((-228780347:ℚ)/1012500000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((84038722993159333475191483491301509647966765724506785279:ℚ)/397125957600000000000000000000000000000000000000000000000),((2155969:ℚ)/128000000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((4226590593:ℚ)/5000000000),((418117961:ℚ)/400000000),((-2210025727:ℚ)/5184000000),((-8039771779:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((505714075944645326321583322000113242408459947496519:ℚ)/2015539200000000000000000000000000000000000000000000),((2155969:ℚ)/128000000)⟩
theorem valid14 : Valid source30 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((10365953949:ℚ)/10000000000),((14268021659:ℚ)/10000000000),((-81956151613:ℚ)/160000000000),((-948602689:ℚ)/4800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1148250867546693037575587:ℚ)/3840000000000000000000000),((2155969:ℚ)/128000000)⟩
theorem valid15 : Valid source30 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC10
#check @N11Formalization.C450Source30GroupedC10.bound
#print axioms N11Formalization.C450Source30GroupedC10.valid0
#print axioms N11Formalization.C450Source30GroupedC10.valid1
#print axioms N11Formalization.C450Source30GroupedC10.valid2
#print axioms N11Formalization.C450Source30GroupedC10.valid3
#print axioms N11Formalization.C450Source30GroupedC10.valid4
#print axioms N11Formalization.C450Source30GroupedC10.valid5
#print axioms N11Formalization.C450Source30GroupedC10.valid6
#print axioms N11Formalization.C450Source30GroupedC10.valid7
#print axioms N11Formalization.C450Source30GroupedC10.valid8
#print axioms N11Formalization.C450Source30GroupedC10.valid9
#print axioms N11Formalization.C450Source30GroupedC10.valid10
#print axioms N11Formalization.C450Source30GroupedC10.valid11
#print axioms N11Formalization.C450Source30GroupedC10.valid12
#print axioms N11Formalization.C450Source30GroupedC10.valid13
#print axioms N11Formalization.C450Source30GroupedC10.valid14
#print axioms N11Formalization.C450Source30GroupedC10.valid15
#print axioms N11Formalization.C450Source30GroupedC10.bound
#print axioms N11Formalization.C450Source30GroupedC10.endpoint_checks
