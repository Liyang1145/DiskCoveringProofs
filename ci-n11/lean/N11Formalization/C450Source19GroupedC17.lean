import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((3056608027:ℚ)/5000000000),((1660068241:ℚ)/2500000000),((136:ℚ)/1335),((4540068241:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3180905499:ℚ)/5000000000),((6414774600719385154363939906454514237853:ℚ)/90614212224000000000000000000000000000000),((-79340285554272077753344773:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6591207499:ℚ)/10000000000),((6878972037:ℚ)/10000000000),((272:ℚ)/2765),((6132990679:ℚ)/35600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5211159531:ℚ)/10000000000),((17547156135777006990321363190959802948905863381069723765606729:ℚ)/258703037905200000000000000000000000000000000000000000000000000),((-4104976997701450495608782231:ℚ)/22179840000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((273201909:ℚ)/400000000),((6998290977:ℚ)/10000000000),((544:ℚ)/5625),((18518290977:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((227010889:ℚ)/500000000),((2174429214430889489097940882300490092966824843127867777721:ℚ)/32614529850000000000000000000000000000000000000000000000000),((-4253148225859883204612121071:ℚ)/22179840000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((694943361:ℚ)/1000000000),((7117590887:ℚ)/10000000000),((68:ℚ)/715),((18637590887:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2083875717:ℚ)/5000000000),((12065273749591478534025869380854192634210960842278739628738379:ℚ)/181974133300781250000000000000000000000000000000000000000000000),((-1442049215736708162564208277:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7068798209:ℚ)/10000000000),((1809218177:ℚ)/2500000000),((544:ℚ)/5815),((4689218177:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((940244091:ℚ)/2500000000),((9784404705362498223527754572533123466177354761779898845430903:ℚ)/148319690166862500000000000000000000000000000000000000000000000),((-91647887630106316700950757:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((449258911:ℚ)/625000000),((7356137321:ℚ)/10000000000),((272:ℚ)/2955),((18876137321:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3307217053:ℚ)/10000000000),((18791479171752333711657910817099330864424926304152001381583759:ℚ)/286162602765576562500000000000000000000000000000000000000000000),((-1490667255303759012284918453:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((1461493539:ℚ)/2000000000),((7475385549:ℚ)/10000000000),((544:ℚ)/6005),((6331795183:ℚ)/39400000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2783544019:ℚ)/10000000000),((108176069195214452818093639099256869471007722988873841516501113:ℚ)/1654154049085950000000000000000000000000000000000000000000000000),((-4544857745155884113951684999:ℚ)/22179840000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((742677449:ℚ)/1000000000),((7594618163:ℚ)/10000000000),((136:ℚ)/1525),((19114618163:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2139156189:ℚ)/10000000000),((2624922771655726441021980118330661527456785224206031822889351:ℚ)/40287350745756250000000000000000000000000000000000000000000000),((-1539222375063323852928165677:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7546063823:ℚ)/10000000000),((2017851581:ℚ)/2500000000),((34:ℚ)/405),((4897851581:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((238416033:ℚ)/2000000000),((6362955419436004833999038523565668617378588546215320106211:ℚ)/96954579492187500000000000000000000000000000000000000000000),((-102907859060952373:ℚ)/486400000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((501441377:ℚ)/625000000),((4988426607:ℚ)/5000000000),((17:ℚ)/250),((1194269623:ℚ)/7200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((29329226754342584891704354761668320142023917801603617:ℚ)/437400000000000000000000000000000000000000000000000000),((-109107207:ℚ)/512000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9929147831:ℚ)/10000000000),((13783236197:ℚ)/10000000000),((17:ℚ)/345),((25303236197:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((122889576818473340923724847410494945167161:ℚ)/1625088000000000000000000000000000000000000),((-109107207:ℚ)/512000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC17
#check @N11Formalization.C450Source19GroupedC17.bound
#print axioms N11Formalization.C450Source19GroupedC17.valid0
#print axioms N11Formalization.C450Source19GroupedC17.valid1
#print axioms N11Formalization.C450Source19GroupedC17.valid2
#print axioms N11Formalization.C450Source19GroupedC17.valid3
#print axioms N11Formalization.C450Source19GroupedC17.valid4
#print axioms N11Formalization.C450Source19GroupedC17.valid5
#print axioms N11Formalization.C450Source19GroupedC17.valid6
#print axioms N11Formalization.C450Source19GroupedC17.valid7
#print axioms N11Formalization.C450Source19GroupedC17.valid8
#print axioms N11Formalization.C450Source19GroupedC17.valid9
#print axioms N11Formalization.C450Source19GroupedC17.valid10
#print axioms N11Formalization.C450Source19GroupedC17.bound
#print axioms N11Formalization.C450Source19GroupedC17.endpoint_checks
