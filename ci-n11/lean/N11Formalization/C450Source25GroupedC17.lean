import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(0:ℚ),((1:ℚ)/16),((23693439:ℚ)/39062500),((6371421057:ℚ)/10000000000),((368:ℚ)/2575),((21731421057:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6466697751:ℚ)/10000000000),((369939893207425975225318706646678414855959:ℚ)/2589103874048000000000000000000000000000000),((-2701595817814219934451124771:ℚ)/8871936000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((6305799731:ℚ)/10000000000),((6611295261:ℚ)/10000000000),((184:ℚ)/1335),((21971295261:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((74025937:ℚ)/125000000),((268254526133817392149935996970671415428746253145991066969881:ℚ)/1901841189038085937500000000000000000000000000000000000000000),((-2803801719184496556671422459:ℚ)/8871936000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((3272939031:ℚ)/5000000000),((1370200807:ℚ)/2000000000),((368:ℚ)/2765),((4442200807:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((333108819:ℚ)/625000000),((371435065226494449463593338734679090483023579474320092853581:ℚ)/2660945532739200000000000000000000000000000000000000000000000),((-38742062536515631371330257:ℚ)/118292480000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((1696444131:ℚ)/2500000000),((3485400859:ℚ)/5000000000),((736:ℚ)/5625),((11165400859:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4671279263:ℚ)/10000000000),((1679960947428336574151985533033397326077762736888244781753:ℚ)/12230448693750000000000000000000000000000000000000000000000),((-250922189910774394177675833:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((431604007:ℚ)/625000000),((1418112831:ℚ)/2000000000),((92:ℚ)/715),((1496704277:ℚ)/7500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((67309487:ℚ)/156250000),((2461142252529120171360385216006265158074176824370839350251:ℚ)/17972753906250000000000000000000000000000000000000000000000),((-122470414759466194329037219:ℚ)/354877440000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((1756378347:ℚ)/2500000000),((7210293101:ℚ)/10000000000),((736:ℚ)/5815),((22570293101:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((391311477:ℚ)/1000000000),((432162001546034576418599140485315955279872583140503904249545689:ℚ)/3164153390226400000000000000000000000000000000000000000000000000),((-1037457221596556203583387593:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7145326261:ℚ)/10000000000),((7329990197:ℚ)/10000000000),((368:ℚ)/2955),((22689990197:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((695308337:ℚ)/2000000000),((12999860089335232997801039532515817671226401105086002204900673:ℚ)/95387534255192187500000000000000000000000000000000000000000000),((-1054300345229632053967157337:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((7265104519:ℚ)/10000000000),((1892323721:ℚ)/2500000000),((184:ℚ)/1525),((5732323721:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2979687099:ℚ)/10000000000),((82208912446613026450868532664088785025494255768896685530901:ℚ)/600084132180468750000000000000000000000000000000000000000000),((-66858041443831160343800113:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((1500912753:ℚ)/2000000000),((8047583491:ℚ)/10000000000),((46:ℚ)/405),((23407583491:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((198303501:ℚ)/1250000000),((2574919079894174354671974999416984053258292832728694736419551:ℚ)/18615279262500000000000000000000000000000000000000000000000000),((-72744625482757687:ℚ)/194560000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((1596626743:ℚ)/2000000000),((1244698759:ℚ)/1250000000),((23:ℚ)/250),((3164698759:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((241857273789645291617020932000143509110337801780913891:ℚ)/1660753125000000000000000000000000000000000000000000000),((-387882727:ℚ)/1024000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9893994171:ℚ)/10000000000),((6884649593:ℚ)/5000000000),((1:ℚ)/15),((14564649593:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((196245265445230517996543810671368656791:ℚ)/1152000000000000000000000000000000000000),((-387882727:ℚ)/1024000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC17
#check @N11Formalization.C450Source25GroupedC17.bound
#print axioms N11Formalization.C450Source25GroupedC17.valid0
#print axioms N11Formalization.C450Source25GroupedC17.valid1
#print axioms N11Formalization.C450Source25GroupedC17.valid2
#print axioms N11Formalization.C450Source25GroupedC17.valid3
#print axioms N11Formalization.C450Source25GroupedC17.valid4
#print axioms N11Formalization.C450Source25GroupedC17.valid5
#print axioms N11Formalization.C450Source25GroupedC17.valid6
#print axioms N11Formalization.C450Source25GroupedC17.valid7
#print axioms N11Formalization.C450Source25GroupedC17.valid8
#print axioms N11Formalization.C450Source25GroupedC17.valid9
#print axioms N11Formalization.C450Source25GroupedC17.valid10
#print axioms N11Formalization.C450Source25GroupedC17.bound
#print axioms N11Formalization.C450Source25GroupedC17.endpoint_checks
