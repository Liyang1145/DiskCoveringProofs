import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5742556103:ℚ)/10000000000),((6283547141:ℚ)/10000000000),((6702556103:ℚ)/10680000000),((79359018551:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7142274897:ℚ)/10000000000),((-3920308265775065932961610276161533:ℚ)/152273304000000000000000000000000000),((-112496167347185153846599613:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1243760113:ℚ)/2000000000),((1304322751:ℚ)/2000000000),((1435760113:ℚ)/2212000000),((16395550261:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6124131247:ℚ)/10000000000),((-3340134033548019337818855661813661693418487586541307:ℚ)/101467426200000000000000000000000000000000000000000000),((-4502193479402049134866373:ℚ)/14786560000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6456858431:ℚ)/10000000000),((33798213:ℚ)/50000000),((7416858431:ℚ)/11440000000),((422980343:ℚ)/553000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5555952333:ℚ)/10000000000),((-155668404611777429575229703722495071373242369518668383:ℚ)/4678731200000000000000000000000000000000000000000000000),((-8437553749631298106411:ℚ)/27724800000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3347439557:ℚ)/5000000000),((3439322011:ℚ)/5000000000),((3827439557:ℚ)/5815000000),((42952542121:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((30814067:ℚ)/62500000),((-16756592417789358879762865421551734176861473996383503:ℚ)/460850902441406250000000000000000000000000000000000000),((-28131243571151007673499133:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1362775331:ℚ)/2000000000),((874704667:ℚ)/1250000000),((1554775331:ℚ)/2364000000),((10901751337:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4588493849:ℚ)/10000000000),((-1127718105713849744233622881064725396692260922437609:ℚ)/30963760650000000000000000000000000000000000000000000),((-1757723532920221645807097:ℚ)/5776000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3466433107:ℚ)/5000000000),((444788933:ℚ)/625000000),((3946433107:ℚ)/6005000000),((5532678263:ℚ)/7387500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((844255613:ℚ)/2000000000),((-74035512094335171489550664778622592229807590899018273:ℚ)/2030066719921875000000000000000000000000000000000000000),((-439305456276368589118147:ℚ)/1444000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((1762962043:ℚ)/2500000000),((7235601161:ℚ)/10000000000),((2002962043:ℚ)/3050000000),((89831612771:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3821238577:ℚ)/10000000000),((-3236910771006299225335372691347924539048764988086579:ℚ)/88664453125000000000000000000000000000000000000000000),((-112428646568630746683096533:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7170822883:ℚ)/10000000000),((58836579:ℚ)/80000000),((8130822883:ℚ)/12390000000),((729122369:ℚ)/976000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1688347043:ℚ)/5000000000),((-6032107553814186733972158865954515840315663095520491:ℚ)/165105461718750000000000000000000000000000000000000000),((-21579581868379345615879:ℚ)/70975488000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1822447671:ℚ)/2500000000),((934192111:ℚ)/1250000000),((2062447671:ℚ)/3145000000),((11556113221:ℚ)/15487500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((358371967:ℚ)/1250000000),((-3469981160528318184080072721290399676433359154303:ℚ)/94931865310668945312500000000000000000000000000000),((-1755581624356832358619733:ℚ)/5776000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7408751889:ℚ)/10000000000),((7711446997:ℚ)/10000000000),((929861321:ℚ)/1440000000),((95065916967:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2248131619:ℚ)/10000000000),((-35324528435911812937495857239310222647454721331057:ℚ)/1036800000000000000000000000000000000000000000000000),((-59112390223041947:ℚ)/194560000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((955831959:ℚ)/1250000000),((961402523:ℚ)/1000000000),((1075831959:ℚ)/2000000000),((11599427753:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-14621866656539393245426611214814823046650345170727:ℚ)/1562500000000000000000000000000000000000000000000000),((-3891949:ℚ)/12800000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9549194159:ℚ)/10000000000),((13417049343:ℚ)/10000000000),((10509194159:ℚ)/22080000000),((157827542773:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((507814808305713998056523:ℚ)/60940800000000000000000000),((-3891949:ℚ)/12800000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC27
#check @N11Formalization.C450Source17GroupedC27.bound
#print axioms N11Formalization.C450Source17GroupedC27.valid0
#print axioms N11Formalization.C450Source17GroupedC27.valid1
#print axioms N11Formalization.C450Source17GroupedC27.valid2
#print axioms N11Formalization.C450Source17GroupedC27.valid3
#print axioms N11Formalization.C450Source17GroupedC27.valid4
#print axioms N11Formalization.C450Source17GroupedC27.valid5
#print axioms N11Formalization.C450Source17GroupedC27.valid6
#print axioms N11Formalization.C450Source17GroupedC27.valid7
#print axioms N11Formalization.C450Source17GroupedC27.valid8
#print axioms N11Formalization.C450Source17GroupedC27.valid9
#print axioms N11Formalization.C450Source17GroupedC27.valid10
#print axioms N11Formalization.C450Source17GroupedC27.valid11
#print axioms N11Formalization.C450Source17GroupedC27.bound
#print axioms N11Formalization.C450Source17GroupedC27.endpoint_checks
