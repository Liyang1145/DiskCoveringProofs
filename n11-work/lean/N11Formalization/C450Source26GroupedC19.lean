import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/8),((3:ℚ)/16),((1186839107:ℚ)/2000000000),((6246647963:ℚ)/10000000000),((2722839107:ℚ)/10300000000),((34739943889:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6748267517:ℚ)/10000000000),((242269154540941836570604439147526288825733:ℚ)/2589103874048000000000000000000000000000000),((-105969023836293710514637937:ℚ)/295731200000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((3087309669:ℚ)/5000000000),((648669547:ℚ)/1000000000),((2309103223:ℚ)/8900000000),((3546008641:ℚ)/10300000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6224544021:ℚ)/10000000000),((19357607155048290605027955639192091772343076777155043591:ℚ)/211315687670898437500000000000000000000000000000000000000),((-1088213675989754488434257:ℚ)/2957312000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6414831499:ℚ)/10000000000),((6726565291:ℚ)/10000000000),((2013547357:ℚ)/7900000000),((36179695873:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2829962577:ℚ)/5000000000),((12836205132806057506132491743303831204349223837059827313931909:ℚ)/142550653539600000000000000000000000000000000000000000000000000),((-111646482105194916002037713:ℚ)/295731200000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6654854307:ℚ)/10000000000),((3423219653:ℚ)/5000000000),((4778284769:ℚ)/18750000000),((18269658959:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1008079179:ℚ)/2000000000),((117263789609456951517289142503832002717412018784753966863:ℚ)/1358938743750000000000000000000000000000000000000000000000),((-28699699682321026813623857:ℚ)/73932800000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((270992033:ℚ)/400000000),((696627547:ℚ)/1000000000),((578192033:ℚ)/2288000000),((3689882641:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4703247617:ℚ)/10000000000),((15628147693725862292496108340344722289757107090057034184879:ℚ)/181974133300781250000000000000000000000000000000000000000000),((-1161939403997669557590257:ℚ)/2957312000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((861838377:ℚ)/1250000000),((7086075673:ℚ)/10000000000),((1821838377:ℚ)/7268750000),((2866017463:ℚ)/8800000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4342204161:ℚ)/10000000000),((33599968260712064236517724281792852661571584138256052568401:ℚ)/392786037600000000000000000000000000000000000000000000000000),((-117582458700539372436607817:ℚ)/295731200000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((3507287447:ℚ)/5000000000),((3602920839:ℚ)/5000000000),((7347287447:ℚ)/29550000000),((18808762517:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3950680379:ℚ)/10000000000),((3050179374154945001239824962850446432056989782218455157012921:ℚ)/35770325345697070312500000000000000000000000000000000000000000),((-29741095774308363062772233:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7134406341:ℚ)/10000000000),((930659699:ℚ)/1250000000),((14814406341:ℚ)/61000000000),((4791979097:ℚ)/14775000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((439809121:ℚ)/1250000000),((19659736578692080135144337881249023302911928141576197625981:ℚ)/225031549567675781250000000000000000000000000000000000000000),((-1874398362777781895639873:ℚ)/4620800000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((7373966869:ℚ)/10000000000),((495237817:ℚ)/625000000),((15053966869:ℚ)/64800000000),((2485713451:ℚ)/7625000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((61124673:ℚ)/250000000),((414470719105541546071407363380692404354171040089364889209:ℚ)/4544745913696289062500000000000000000000000000000000000000),((-50558039487497701:ℚ)/121600000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((3926360577:ℚ)/5000000000),((9834536657:ℚ)/10000000000),((7766360577:ℚ)/40000000000),((45503609971:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((280288173707458028028217034464350451432762672650787232623:ℚ)/2550916800000000000000000000000000000000000000000000000000),((-218582963:ℚ)/512000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((122051761:ℚ)/125000000),((13647091199:ℚ)/10000000000),((218051761:ℚ)/1380000000),((56941273597:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((720173818135334179384073339477025877225969:ℚ)/4875264000000000000000000000000000000000000),((-218582963:ℚ)/512000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC19
#check @N11Formalization.C450Source26GroupedC19.bound
#print axioms N11Formalization.C450Source26GroupedC19.valid0
#print axioms N11Formalization.C450Source26GroupedC19.valid1
#print axioms N11Formalization.C450Source26GroupedC19.valid2
#print axioms N11Formalization.C450Source26GroupedC19.valid3
#print axioms N11Formalization.C450Source26GroupedC19.valid4
#print axioms N11Formalization.C450Source26GroupedC19.valid5
#print axioms N11Formalization.C450Source26GroupedC19.valid6
#print axioms N11Formalization.C450Source26GroupedC19.valid7
#print axioms N11Formalization.C450Source26GroupedC19.valid8
#print axioms N11Formalization.C450Source26GroupedC19.valid9
#print axioms N11Formalization.C450Source26GroupedC19.valid10
#print axioms N11Formalization.C450Source26GroupedC19.bound
#print axioms N11Formalization.C450Source26GroupedC19.endpoint_checks
