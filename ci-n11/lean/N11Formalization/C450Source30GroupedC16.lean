import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/16),(0:ℚ),((6090517217:ℚ)/10000000000),((6409708691:ℚ)/10000000000),((11510291309:ℚ)/103000000000),((29:ℚ)/155),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((256476457:ℚ)/400000000),((-179318773861948773331932178727785433232362905019038384879:ℚ)/6829543750000000000000000000000000000000000000000000000000),((-107393189794609239:ℚ)/486400000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((6332124937:ℚ)/10000000000),((6650738943:ℚ)/10000000000),((11269261057:ℚ)/106800000000),((464:ℚ)/2575),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5859731223:ℚ)/10000000000),((-4820973738363194869564055339699121346260424654827932587:ℚ)/211490700000000000000000000000000000000000000000000000000),((-112564118566538479:ℚ)/486400000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6573433271:ℚ)/10000000000),((3385579767:ℚ)/5000000000),((5574420233:ℚ)/54350000000),((232:ℚ)/1335),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5257945489:ℚ)/10000000000),((-21450749850124213600358693402187506027695657056267928147:ℚ)/1003410549218750000000000000000000000000000000000000000000),((-117728639829298257:ℚ)/486400000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((6693985287:ℚ)/10000000000),((430720097:ℚ)/625000000),((689279903:ℚ)/6912500000),((928:ℚ)/5435),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4932735051:ℚ)/10000000000),((-638917438795493900732382522022975247346352929656653:ℚ)/32255626106262207031250000000000000000000000000000000),((-120308714207916929:ℚ)/486400000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((6814474023:ℚ)/10000000000),((1752957011:ℚ)/2500000000),((2727042989:ℚ)/28125000000),((464:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4586718907:ℚ)/10000000000),((-122711644098206234473971793414676705368653615224239:ℚ)/6705522537231445312500000000000000000000000000000000),((-122887434257407841:ℚ)/486400000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((6934902777:ℚ)/10000000000),((7132081849:ℚ)/10000000000),((10787918151:ℚ)/114400000000),((928:ℚ)/5625),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4214732723:ℚ)/10000000000),((-157673922376928699762129549381075019048013043849068857381:ℚ)/9357462400000000000000000000000000000000000000000000000000),((-6603414240111461:ℚ)/25600000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((352763731:ℚ)/500000000),((7372441803:ℚ)/10000000000),((10547558197:ℚ)/118200000000),((116:ℚ)/715),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3809129741:ℚ)/10000000000),((-4005120996344725779162290972639089149118207880912071367:ℚ)/286701487500000000000000000000000000000000000000000000000),((-6402054442405077:ℚ)/24320000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((182396471:ℚ)/250000000),((951577571:ℚ)/1250000000),((1288422429:ℚ)/15250000000),((464:ℚ)/2955),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((567720873:ℚ)/2000000000),((-253561819331861132521067459616698149364269637297316519:ℚ)/22166113281250000000000000000000000000000000000000000000),((-3329752812552657:ℚ)/12160000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((3768123703:ℚ)/5000000000),((8092499613:ℚ)/10000000000),((9827500387:ℚ)/129600000000),((232:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1296167687:ℚ)/10000000000),((-124429712659714919853611431038468862320106410604168577:ℚ)/18662400000000000000000000000000000000000000000000000000),((-69167474368264401:ℚ)/243200000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((1603301593:ℚ)/2000000000),((10007328617:ℚ)/10000000000),((7912671383:ℚ)/160000000000),((58:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((193529734356312214382374873915104444196234062141774149483:ℚ)/25600000000000000000000000000000000000000000000000000000000),((-18381499:ℚ)/64000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((2483123033:ℚ)/2500000000),((43202043:ℚ)/31250000),((12797957:ℚ)/690000000),((29:ℚ)/250),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1525356888363836645074872294644421904153494285433:ℚ)/57032812500000000000000000000000000000000000000000),((-18381499:ℚ)/64000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC16
#check @N11Formalization.C450Source30GroupedC16.bound
#print axioms N11Formalization.C450Source30GroupedC16.valid0
#print axioms N11Formalization.C450Source30GroupedC16.valid1
#print axioms N11Formalization.C450Source30GroupedC16.valid2
#print axioms N11Formalization.C450Source30GroupedC16.valid3
#print axioms N11Formalization.C450Source30GroupedC16.valid4
#print axioms N11Formalization.C450Source30GroupedC16.valid5
#print axioms N11Formalization.C450Source30GroupedC16.valid6
#print axioms N11Formalization.C450Source30GroupedC16.valid7
#print axioms N11Formalization.C450Source30GroupedC16.valid8
#print axioms N11Formalization.C450Source30GroupedC16.valid9
#print axioms N11Formalization.C450Source30GroupedC16.valid10
#print axioms N11Formalization.C450Source30GroupedC16.bound
#print axioms N11Formalization.C450Source30GroupedC16.endpoint_checks
