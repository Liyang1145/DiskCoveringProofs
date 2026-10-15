import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6511968889:ℚ)/10000000000),((1703729159:ℚ)/2500000000),((-12613562431:ℚ)/24800000000),((-5071968889:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((216676431:ℚ)/400000000),((93980474627158397879652956402956077697576301395118860351:ℚ)/1240522595214843750000000000000000000000000000000000000000),((1718150522795047233777297677:ℚ)/7393280000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1350101497:ℚ)/2000000000),((6934168331:ℚ)/10000000000),((-51527514979:ℚ)/103000000000),((-1062101497:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((954660179:ℚ)/2000000000),((212311999693204961688844267729174871001810002246506373:ℚ)/2902710616381835937500000000000000000000000000000000000),((67711293584730049745003533:ℚ)/295731200000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6869748389:ℚ)/10000000000),((6993787383:ℚ)/10000000000),((-52064086447:ℚ)/104900000000),((-5429748389:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4419619241:ℚ)/10000000000),((1092123254069441321730128644769897237879267448557191613343:ℚ)/15186515286311340332031250000000000000000000000000000000000),((1680008769620862197144534677:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((6929362193:ℚ)/10000000000),((3526701033:ℚ)/5000000000),((-26300309297:ℚ)/52925000000),((-5489362193:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2116258713:ℚ)/5000000000),((566135299664182484578583791067227170572987192274572943967:ℚ)/7870180287304687500000000000000000000000000000000000000000),((1673599579374780356891780413:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((6988971723:ℚ)/10000000000),((3556506249:ℚ)/5000000000),((-26568556241:ℚ)/53400000000),((-5548971723:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2018656583:ℚ)/5000000000),((381998220465810994630806733401301942704413745987080809:ℚ)/5308990328758955001831054687500000000000000000000000000),((4618214514769618050915693:ℚ)/20480000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7048577093:ℚ)/10000000000),((7172618791:ℚ)/10000000000),((-53673569119:ℚ)/107750000000),((-5608577093:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1916382203:ℚ)/5000000000),((486330186395816204511037166282650631581624269806664112881:ℚ)/6757342917395019531250000000000000000000000000000000000000),((1660736341976311239367072213:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7108178413:ℚ)/10000000000),((7232221053:ℚ)/10000000000),((-54209989477:ℚ)/108700000000),((-5668178413:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1808640899:ℚ)/5000000000),((104939160747600179187069563571274141308793450174019726179:ℚ)/1457754069386672973632812500000000000000000000000000000000),((1654282277108086664513041253:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7167775789:ℚ)/10000000000),((1822954847:ℚ)/2500000000),((-13686593623:ℚ)/27412500000),((-72503491:ℚ)/175000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((423596941:ℚ)/1250000000),((82641191464576361752458826746932609619572085000401:ℚ)/1147764587402343750000000000000000000000000000000000),((1647813236847791461919151077:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((289094773:ℚ)/400000000),((7351413899:ℚ)/10000000000),((-55282725091:ℚ)/110600000000),((-231494773:ℚ)/557750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3144402557:ℚ)/10000000000),((2699172332315847440259582768234409803974157381670087:ℚ)/37480372877337646484375000000000000000000000000000000),((2626126740678629625918773:ℚ)/11829248000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((3643479559:ℚ)/5000000000),((3705502341:ℚ)/5000000000),((-27909521069:ℚ)/55775000000),((-2923479559:ℚ)/7031250000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((720030391:ℚ)/2500000000),((4091295687602751280103795850712167558932446823346304001:ℚ)/56801328901201486587524414062500000000000000000000000000),((408707549430626551759171597:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7346545263:ℚ)/10000000000),((7530175439:ℚ)/10000000000),((-56891578951:ℚ)/112500000000),((-5906545263:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2589839247:ℚ)/10000000000),((4010540841246489713803782764532405534110066044284077863:ℚ)/54828881250000000000000000000000000000000000000000000000),((4510571146112737547701173:ℚ)/20480000000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((373285349:ℚ)/500000000),((7768476169:ℚ)/10000000000),((-59036285521:ℚ)/114400000000),((-301285349:ℚ)/738750000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((376535999:ℚ)/2000000000),((22825144998557285687604838918810695084279504486873:ℚ)/303313748168945312500000000000000000000000000000000),((4038107824964374232988437:ℚ)/18483200000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((7703990509:ℚ)/10000000000),((400336339:ℚ)/500000000),((-3059027051:ℚ)/5910000000),((-102688369:ℚ)/250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((4335658089668246139649843168925077213659627596169797:ℚ)/57714843750000000000000000000000000000000000000000000),((22166707:ℚ)/102400000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((7942225001:ℚ)/10000000000),((1060386923:ℚ)/1250000000),((-8183482307:ℚ)/15250000000),((-6502225001:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((697029501315295243851408020767960396277909210630928161:ℚ)/8857350000000000000000000000000000000000000000000000000),((22166707:ℚ)/102400000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((4209282113:ℚ)/5000000000),((10387265527:ℚ)/10000000000),((-82605389743:ℚ)/129600000000),((-3489282113:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3924430535763919193713044841304093296944806132258783894983:ℚ)/40814668800000000000000000000000000000000000000000000000000),((22166707:ℚ)/102400000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((5161322469:ℚ)/5000000000),((283843087:ℚ)/200000000),((-2336987783:ℚ)/3200000000),((-1480440823:ℚ)/4600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((9542079767543038006587108882261765100120952400400210247:ℚ)/81254400000000000000000000000000000000000000000000000000),((22166707:ℚ)/102400000)⟩
theorem valid15 : Valid source19 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC08
#check @N11Formalization.C450Source19GroupedC08.bound
#print axioms N11Formalization.C450Source19GroupedC08.valid0
#print axioms N11Formalization.C450Source19GroupedC08.valid1
#print axioms N11Formalization.C450Source19GroupedC08.valid2
#print axioms N11Formalization.C450Source19GroupedC08.valid3
#print axioms N11Formalization.C450Source19GroupedC08.valid4
#print axioms N11Formalization.C450Source19GroupedC08.valid5
#print axioms N11Formalization.C450Source19GroupedC08.valid6
#print axioms N11Formalization.C450Source19GroupedC08.valid7
#print axioms N11Formalization.C450Source19GroupedC08.valid8
#print axioms N11Formalization.C450Source19GroupedC08.valid9
#print axioms N11Formalization.C450Source19GroupedC08.valid10
#print axioms N11Formalization.C450Source19GroupedC08.valid11
#print axioms N11Formalization.C450Source19GroupedC08.valid12
#print axioms N11Formalization.C450Source19GroupedC08.valid13
#print axioms N11Formalization.C450Source19GroupedC08.valid14
#print axioms N11Formalization.C450Source19GroupedC08.valid15
#print axioms N11Formalization.C450Source19GroupedC08.bound
#print axioms N11Formalization.C450Source19GroupedC08.endpoint_checks
