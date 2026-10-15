import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((2707308387:ℚ)/5000000000),((5978495691:ℚ)/10000000000),((12486797419:ℚ)/17800000000),((21935487073:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7778134751:ℚ)/10000000000),((-296326071671132235474012138035457793:ℚ)/1409938000000000000000000000000000000),((-352698540789122248035089291:ℚ)/887193600000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((5892147617:ℚ)/10000000000),((124345129:ℚ)/200000000),((80173623787:ℚ)/110600000000),((453035387:ℚ)/534000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3418169799:ℚ)/5000000000),((-6008592146065591308115749548604584574787699363345551966209:ℚ)/25366856550000000000000000000000000000000000000000000000000),((-46484738863126833660017:ℚ)/118292480000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((6130781657:ℚ)/10000000000),((792075581:ℚ)/1250000000),((82798598227:ℚ)/112500000000),((2876226743:ℚ)/3456250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1580701533:ℚ)/2500000000),((-739453744258336174557420323174430932434083971248415120809:ℚ)/2966308593750000000000000000000000000000000000000000000000),((-1805029003182017935390057:ℚ)/4620800000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((781258719:ℚ)/1250000000),((645593283:ℚ)/1000000000),((10513845909:ℚ)/14300000000),((2336779849:ℚ)/2812500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3026094299:ℚ)/5000000000),((-413626796456207730619674945062044740639309430009326311:ℚ)/1661481250000000000000000000000000000000000000000000000),((-3444699402315524325841979:ℚ)/8871936000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((1273867971:ℚ)/2000000000),((6515589727:ℚ)/10000000000),((5694849227:ℚ)/7690000000),((1811289937:ℚ)/2200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((721323143:ℚ)/1250000000),((-543168365166116775508289623902348332962417676443277809:ℚ)/2131671604687500000000000000000000000000000000000000000),((-114470834588178974363434273:ℚ)/295731200000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6428968439:ℚ)/10000000000),((3287620993:ℚ)/5000000000),((86078652829:ℚ)/116300000000),((11862862979:ℚ)/14418750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((5625142497:ℚ)/10000000000),((-100110827902257314695532179495651645373790816438874469869:ℚ)/393259436750000000000000000000000000000000000000000000000),((-28529054309113324516876513:ℚ)/73932800000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((1297718571:ℚ)/2000000000),((3317444861:ℚ)/5000000000),((2478129183:ℚ)/3350000000),((11952334583:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1369068651:ℚ)/2500000000),((-14939799001863563970202172964804974135982750385554423:ℚ)/58742773437500000000000000000000000000000000000000000),((-28439865292655096183443177:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1309642641:ℚ)/2000000000),((6694533043:ℚ)/10000000000),((5826023017:ℚ)/7880000000),((24083599129:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2661845409:ℚ)/5000000000),((-194257565580988593302897520057487354984592720656094377:ℚ)/764537300000000000000000000000000000000000000000000000),((-113400566231470336952367113:ℚ)/295731200000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3303914793:ℚ)/5000000000),((3377086029:ℚ)/5000000000),((44023062723:ℚ)/59575000000),((12131258087:ℚ)/14775000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1033411719:ℚ)/2000000000),((-335460057982100681950941862791774885257516523181372035627:ℚ)/1321515223339843750000000000000000000000000000000000000000),((-84779649178501956373044251:ℚ)/221798400000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1333488419:ℚ)/2000000000),((1703451717:ℚ)/2500000000),((17740372609:ℚ)/24020000000),((6110355151:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((625749313:ℚ)/1250000000),((-1372895207150281338139923621775342278133253077388774529:ℚ)/5413511253125000000000000000000000000000000000000000000),((-21126817320416306299471979:ℚ)/55449600000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((840881353:ℚ)/1250000000),((433316517:ℚ)/625000000),((11169694883:ℚ)/15250000000),((1549949551:ℚ)/1876562500),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4840052627:ℚ)/10000000000),((-5487621144720573433553443641254483732699764950032762107:ℚ)/22166113281250000000000000000000000000000000000000000000),((-1311838996982177136267179:ℚ)/3465600000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((68462573:ℚ)/100000000),((7052306017:ℚ)/10000000000),((906688303:ℚ)/1239000000),((25156918051:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((4491342671:ℚ)/10000000000),((-81631409320153279952162569095680152371634782192143:ℚ)/330210923437500000000000000000000000000000000000000),((-111202271143117793416863393:ℚ)/295731200000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6965449697:ℚ)/10000000000),((7171532819:ℚ)/10000000000),((91979946667:ℚ)/125800000000),((25514598457:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((128605733:ℚ)/312500000),((-2999502671326596979448359042395169324447249284628183387:ℚ)/12151278759765625000000000000000000000000000000000000000),((-110452388124316609392720457:ℚ)/295731200000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((3542314329:ℚ)/5000000000),((92624303:ℚ)/125000000),((15548485873:ℚ)/21600000000),((327872909:ℚ)/393125000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1851926013:ℚ)/5000000000),((-550447321834473064222550991509693133372151180807222259:ℚ)/2332800000000000000000000000000000000000000000000000000),((-17019834174774891125633:ℚ)/46208000000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7322948653:ℚ)/10000000000),((4657835203:ℚ)/5000000000),((95912435183:ℚ)/160000000000),((15973505609:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1354211711:ℚ)/5000000000),((-626836113576204996570113393794008702315390172581515802109:ℚ)/4800000000000000000000000000000000000000000000000000000000),((-186437163:ℚ)/512000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9228101019:ℚ)/10000000000),((6561190029:ℚ)/5000000000),((38956370403:ℚ)/73600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-6186210943585836728787136421117799929:ℚ)/99672064000000000000000000000000000000),((-186437163:ℚ)/512000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source26 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source26 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC28
#check @N11Formalization.C450Source26GroupedC28.bound
#print axioms N11Formalization.C450Source26GroupedC28.valid0
#print axioms N11Formalization.C450Source26GroupedC28.valid1
#print axioms N11Formalization.C450Source26GroupedC28.valid2
#print axioms N11Formalization.C450Source26GroupedC28.valid3
#print axioms N11Formalization.C450Source26GroupedC28.valid4
#print axioms N11Formalization.C450Source26GroupedC28.valid5
#print axioms N11Formalization.C450Source26GroupedC28.valid6
#print axioms N11Formalization.C450Source26GroupedC28.valid7
#print axioms N11Formalization.C450Source26GroupedC28.valid8
#print axioms N11Formalization.C450Source26GroupedC28.valid9
#print axioms N11Formalization.C450Source26GroupedC28.valid10
#print axioms N11Formalization.C450Source26GroupedC28.valid11
#print axioms N11Formalization.C450Source26GroupedC28.valid12
#print axioms N11Formalization.C450Source26GroupedC28.valid13
#print axioms N11Formalization.C450Source26GroupedC28.valid14
#print axioms N11Formalization.C450Source26GroupedC28.valid15
#print axioms N11Formalization.C450Source26GroupedC28.bound
#print axioms N11Formalization.C450Source26GroupedC28.endpoint_checks
