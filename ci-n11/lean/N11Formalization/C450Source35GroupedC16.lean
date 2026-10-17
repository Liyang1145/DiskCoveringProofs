import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/16),(0:ℚ),((1209799983:ℚ)/2000000000),((3191877419:ℚ)/5000000000),((7368122581:ℚ)/51500000000),((34:ℚ)/155),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3251344449:ℚ)/5000000000),((-114479965332742127974353445818725529864327696795742532138029:ℚ)/820398942968750000000000000000000000000000000000000000000000),((-1506869346901019:ℚ)/7782400000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6292202017:ℚ)/10000000000),((6505024453:ℚ)/10000000000),((14614975547:ℚ)/104900000000),((544:ℚ)/2575),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1488512977:ℚ)/2500000000),((-2603163134624747957317825691522544653571761095862286033633467:ℚ)/19134668383189062500000000000000000000000000000000000000000000),((-7919163718084981:ℚ)/38912000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((1282728561:ℚ)/2000000000),((132524033:ℚ)/200000000),((289875967:ℚ)/2136000000),((1088:ℚ)/5245),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((5662841147:ℚ)/10000000000),((-246917872706704407087562543413632035432080218791261035143:ℚ)/1861796622165600000000000000000000000000000000000000000000),((-1622263725370373:ℚ)/7782400000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/16),(0:ℚ),((1306996939:ℚ)/2000000000),((3343378591:ℚ)/5000000000),((7216621409:ℚ)/53875000000),((272:ℚ)/1335),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((214315357:ℚ)/400000000),((-3962132389188424642454851795864155565161571156545175641041:ℚ)/30240008912611007690429687500000000000000000000000000000000),((-1660663410001127:ℚ)/7782400000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((329781013:ℚ)/500000000),((6747291471:ℚ)/10000000000),((14372708529:ℚ)/108700000000),((2176:ℚ)/10775),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2599742469:ℚ)/5000000000),((-192982223433256319010907668846525098574129514393541321312444121:ℚ)/1491156376267393750000000000000000000000000000000000000000000000),((-419963014002809:ℚ)/1945600000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((832029137:ℚ)/1250000000),((680780509:ℚ)/1000000000),((1431219491:ℚ)/10965000000),((1088:ℚ)/5435),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((314789891:ℚ)/625000000),((-34575857783821786427900126644591967478772431037705776490859:ℚ)/270434760264245507812500000000000000000000000000000000000000),((-1061895943271141:ℚ)/4864000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((335841191:ℚ)/500000000),((214634331:ℚ)/312500000),((63623667:ℚ)/493750000),((128:ℚ)/645),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4868892049:ℚ)/10000000000),((-2745699165470747894877990176091873268112030048568147:ℚ)/21734931731224060058593750000000000000000000000000000),((-429551991230963:ℚ)/1945600000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((271095721:ℚ)/400000000),((3494613681:ℚ)/5000000000),((2355128773:ℚ)/18750000000),((544:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4695715621:ℚ)/10000000000),((-3659089694695299938651086421593512697381485294446248423:ℚ)/29665231704711914062500000000000000000000000000000000000),((-347475122148253:ℚ)/1556480000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((862308643:ℚ)/1250000000),((7110081823:ℚ)/10000000000),((14009918177:ℚ)/114400000000),((1088:ℚ)/5625),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((216521139:ℚ)/500000000),((-30456069003498155468111641018864821441651897679252909909259:ℚ)/252651484800000000000000000000000000000000000000000000000000),((-1109806993658399:ℚ)/4864000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7019465789:ℚ)/10000000000),((918947831:ℚ)/1250000000),((1721052169:ℚ)/14775000000),((136:ℚ)/715),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1966962907:ℚ)/5000000000),((-1319799125162261994335131857777702256333082061643692194281:ℚ)/11450700620874023437500000000000000000000000000000000000000),((-9069908093674177:ℚ)/38912000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((7261236549:ℚ)/10000000000),((1898207077:ℚ)/2500000000),((3381792923:ℚ)/30500000000),((544:ℚ)/2955),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2996974277:ℚ)/10000000000),((-760489792912180487036098301341287081424277113651600877564627:ℚ)/6881957522656250000000000000000000000000000000000000000000000),((-9452460274826857:ℚ)/38912000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((7502734499:ℚ)/10000000000),((4037323269:ℚ)/5000000000),((724741859:ℚ)/7200000000),((272:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((80079599:ℚ)/500000000),((-32807506256909134468776938329536156205545231330250048673:ℚ)/321494400000000000000000000000000000000000000000000000000),((-9834580790626207:ℚ)/38912000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((1996252739:ℚ)/2500000000),((2498835119:ℚ)/2500000000),((2781164881:ℚ)/40000000000),((68:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-22874505858394184226941278820088315318158379637815263773721:ℚ)/291600000000000000000000000000000000000000000000000000000000),((-32856853:ℚ)/128000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((9907088369:ℚ)/10000000000),((172743403:ℚ)/125000000),((91256597:ℚ)/2760000000),((17:ℚ)/125),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-570307457892863956801908096200935157476194874126919:ℚ)/10950300000000000000000000000000000000000000000000000),((-32856853:ℚ)/128000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC16
#check @N11Formalization.C450Source35GroupedC16.bound
#print axioms N11Formalization.C450Source35GroupedC16.valid0
#print axioms N11Formalization.C450Source35GroupedC16.valid1
#print axioms N11Formalization.C450Source35GroupedC16.valid2
#print axioms N11Formalization.C450Source35GroupedC16.valid3
#print axioms N11Formalization.C450Source35GroupedC16.valid4
#print axioms N11Formalization.C450Source35GroupedC16.valid5
#print axioms N11Formalization.C450Source35GroupedC16.valid6
#print axioms N11Formalization.C450Source35GroupedC16.valid7
#print axioms N11Formalization.C450Source35GroupedC16.valid8
#print axioms N11Formalization.C450Source35GroupedC16.valid9
#print axioms N11Formalization.C450Source35GroupedC16.valid10
#print axioms N11Formalization.C450Source35GroupedC16.valid11
#print axioms N11Formalization.C450Source35GroupedC16.valid12
#print axioms N11Formalization.C450Source35GroupedC16.valid13
#print axioms N11Formalization.C450Source35GroupedC16.bound
#print axioms N11Formalization.C450Source35GroupedC16.endpoint_checks
