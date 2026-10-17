import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((6309522633:ℚ)/10000000000),((3295241857:ℚ)/5000000000),((-2463241857:ℚ)/9920000000),((-4069522633:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1182658701:ℚ)/2000000000),((174980541636569368236699241138865630770069740154983396953:ℚ)/3308060253906250000000000000000000000000000000000000000000),((9967782065058847839681223:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((3273890237:ℚ)/5000000000),((6828769611:ℚ)/10000000000),((-5164769611:ℚ)/20600000000),((-2153890237:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((16640039:ℚ)/31250000),((6701899197309062454433282806301092257334077901255625007:ℚ)/127637941992187500000000000000000000000000000000000000000),((2298069770643784040343583:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6785984147:ℚ)/10000000000),((434243241:ℚ)/625000000),((-330243241:ℚ)/1335000000),((-4545984147:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4670672579:ℚ)/10000000000),((1724128506021371279195360585451952430348318483983183354879:ℚ)/33488827080175781250000000000000000000000000000000000000000),((8415999848404074741807663:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((107891679:ℚ)/156250000),((7007448119:ℚ)/10000000000),((-5343448119:ℚ)/21740000000),((-145783358:ℚ)/856640625),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2154843419:ℚ)/5000000000),((4034166913296363160051245462728851809302499995370241:ℚ)/79088219910301268100738525390625000000000000000000000),((3919708747124223023399:ℚ)/112812500000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((174115119:ℚ)/250000000),((3533500627:ℚ)/5000000000),((-900500209:ℚ)/3655000000),((-118115119:ℚ)/691250000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4118161833:ℚ)/10000000000),((1201347379621703080350673531083222260953382655984619:ℚ)/23578862683677673339843750000000000000000000000000000),((4895793926057906549227:ℚ)/144400000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3512069633:ℚ)/5000000000),((7126551341:ℚ)/10000000000),((-5462551341:ℚ)/22120000000),((-2392069633:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((979463153:ℚ)/2500000000),((29805275408411196176416790909987718893878430683457102831:ℚ)/585630826208400726318359375000000000000000000000000000000),((1909731670812189789645223:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7083671043:ℚ)/10000000000),((7186098459:ℚ)/10000000000),((-5522098459:ℚ)/22310000000),((-4843671043:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((370733143:ℚ)/1000000000),((20535619995360604554243728233522678002000303994500630721:ℚ)/403920561075210571289062500000000000000000000000000000000),((7444532501821194773523343:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7143200163:ℚ)/10000000000),((7245642681:ℚ)/10000000000),((-5581642681:ℚ)/22500000000),((-4903200163:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((696948719:ℚ)/2000000000),((162955566395907314328186181447608683070579689790801133:ℚ)/3208455809967041015625000000000000000000000000000000000),((7250087510375576741906383:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((1800681673:ℚ)/2500000000),((7305184081:ℚ)/10000000000),((-5641184081:ℚ)/22690000000),((-112789243:ℚ)/650000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3247604293:ℚ)/10000000000),((197609170050278656915777550284035597059239905395824377:ℚ)/3894525781250000000000000000000000000000000000000000000),((440974468824792280423903:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3631125347:ℚ)/5000000000),((7364722729:ℚ)/10000000000),((-438517133:ℚ)/1760000000),((-2511125347:ℚ)/14418750000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2992451113:ℚ)/10000000000),((136032843348777436606831462163240186868068933053441:ℚ)/2683455007731914520263671875000000000000000000000000),((1715261068210723600907263:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((7321772233:ℚ)/10000000000),((7424258693:ℚ)/10000000000),((-1920086231:ℚ)/7690000000),((-5081772233:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1357101547:ℚ)/5000000000),((5983137775524860449083289623020805351292581368676732766903:ℚ)/118131447992480468750000000000000000000000000000000000000000),((6666445623616516323316423:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((738129137:ℚ)/1000000000),((7543322827:ℚ)/10000000000),((-5879322827:ℚ)/23260000000),((-171376379:ℚ)/985000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2404851101:ℚ)/10000000000),((88422876781074680314479794456903919352407348019038023:ℚ)/1736634531054687500000000000000000000000000000000000000),((64717953613763823243783:ℚ)/2310400000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7500322667:ℚ)/10000000000),((121584713:ℚ)/156250000),((-31861571:ℚ)/123125000),((-5260322667:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((162137031:ℚ)/1000000000),((1796526425692317003066303564421166922858466866424763112569:ℚ)/34933794531250000000000000000000000000000000000000000000000),((6082339277163046820182623:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((967294861:ℚ)/1250000000),((1651502707:ℚ)/2000000000),((-1318702707:ℚ)/4880000000),((-229098287:ℚ)/1350000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1818971542160015122523583943052099198377197677202431:ℚ)/34741406250000000000000000000000000000000000000000000),((3188933:ℚ)/128000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((1642867341:ℚ)/2000000000),((10160841229:ℚ)/10000000000),((-8496841229:ℚ)/25920000000),((-1194867341:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((14919215376167042140931356925753011568449867833765402859:ℚ)/259200000000000000000000000000000000000000000000000000000),((3188933:ℚ)/128000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((2023463391:ℚ)/2000000000),((6982371737:ℚ)/5000000000),((-6150371737:ℚ)/16000000000),((-1575463391:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((15147879479824042387548949578745617262058423692300801:ℚ)/233606400000000000000000000000000000000000000000000000),((3188933:ℚ)/128000000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC12
#check @N11Formalization.C450Source15GroupedC12.bound
#print axioms N11Formalization.C450Source15GroupedC12.valid0
#print axioms N11Formalization.C450Source15GroupedC12.valid1
#print axioms N11Formalization.C450Source15GroupedC12.valid2
#print axioms N11Formalization.C450Source15GroupedC12.valid3
#print axioms N11Formalization.C450Source15GroupedC12.valid4
#print axioms N11Formalization.C450Source15GroupedC12.valid5
#print axioms N11Formalization.C450Source15GroupedC12.valid6
#print axioms N11Formalization.C450Source15GroupedC12.valid7
#print axioms N11Formalization.C450Source15GroupedC12.valid8
#print axioms N11Formalization.C450Source15GroupedC12.valid9
#print axioms N11Formalization.C450Source15GroupedC12.valid10
#print axioms N11Formalization.C450Source15GroupedC12.valid11
#print axioms N11Formalization.C450Source15GroupedC12.valid12
#print axioms N11Formalization.C450Source15GroupedC12.valid13
#print axioms N11Formalization.C450Source15GroupedC12.valid14
#print axioms N11Formalization.C450Source15GroupedC12.valid15
#print axioms N11Formalization.C450Source15GroupedC12.bound
#print axioms N11Formalization.C450Source15GroupedC12.endpoint_checks
