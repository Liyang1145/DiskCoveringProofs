import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((1480081199:ℚ)/2500000000),((6458495691:ℚ)/10000000000),((2200081199:ℚ)/6675000000),((8890495691:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6777427103:ℚ)/10000000000),((3337445738001120437230970077146868248977:ℚ)/69591714988032000000000000000000000000000),((-2551153411233974091816945623:ℚ)/8871936000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((799793053:ℚ)/1250000000),((133945129:ℚ)/200000000),((1159793053:ℚ)/3456250000),((182585129:ℚ)/427200000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((712531389:ℚ)/1250000000),((9612570254764542268886452194854478607281794339804858587:ℚ)/223519424750092800000000000000000000000000000000000000000),((-353188244005034695025301:ℚ)/1182924800000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((414824829:ℚ)/625000000),((693593283:ℚ)/1000000000),((594824829:ℚ)/1787500000),((936793283:ℚ)/2212000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2544146389:ℚ)/5000000000),((320574173864733482625130123803230772001170010731633193:ℚ)/7600393400600000000000000000000000000000000000000000000),((-26926531156312902137615687:ℚ)/88719360000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6875959511:ℚ)/10000000000),((3527620993:ℚ)/5000000000),((9755959511:ℚ)/29075000000),((4743620993:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2200236509:ℚ)/5000000000),((191276087573933995600404876271461808881871892058345660486811:ℚ)/4746230085339600000000000000000000000000000000000000000000000),((-228431456062061903767022789:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3497654733:ℚ)/5000000000),((7174533043:ℚ)/10000000000),((1645884911:ℚ)/4925000000),((9606533043:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2008016501:ℚ)/5000000000),((15279965134120036236184020780768391444940485254407129009683:ℚ)/381550137020768750000000000000000000000000000000000000000000),((-920939059657838692283144589:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((889329999:ℚ)/1250000000),((1823451717:ℚ)/2500000000),((1249329999:ℚ)/3753125000),((2431451717:ℚ)/5910000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3593180457:ℚ)/10000000000),((111169347061962365259471429176386968030956397900637764347311:ℚ)/2791384957832540625000000000000000000000000000000000000000000),((-9159102027027632749389773:ℚ)/29184000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((7233952019:ℚ)/10000000000),((463316517:ℚ)/625000000),((10113952019:ℚ)/30500000000),((615316517:ℚ)/1501250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((311627611:ℚ)/1000000000),((1559379669430765894869264769767054327664769059028174637:ℚ)/39343115962652587890625000000000000000000000000000000000),((-10960262477040868453716287:ℚ)/34656000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((367662321:ℚ)/500000000),((7651532819:ℚ)/10000000000),((511662321:ℚ)/1572500000),((10083532819:ℚ)/24400000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2555183131:ℚ)/10000000000),((182232687689692729989192126649791667216463180185629363719731:ℚ)/4490149491050000000000000000000000000000000000000000000000000),((-15482965096498519:ℚ)/48640000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((1518357113:ℚ)/2000000000),((98624303:ℚ)/125000000),((2094357113:ℚ)/6480000000),((129024303:ℚ)/314500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((464982039:ℚ)/10000000000),((25703878419522533589733522339740868931274053704741327:ℚ)/637796319542578125000000000000000000000000000000000000),((-63105856502631407:ℚ)/194560000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((1957565849:ℚ)/2500000000),((4897835203:ℚ)/5000000000),((2677565849:ℚ)/10000000000),((6113835203:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((65399413553845528653513626057205397865723013617941081:ℚ)/1275458400000000000000000000000000000000000000000000000),((-332348867:ℚ)/1024000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((4868203133:ℚ)/5000000000),((6801190029:ℚ)/5000000000),((6308203133:ℚ)/27600000000),((8017190029:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6440772335421114712535939:ℚ)/95220000000000000000000000),((-332348867:ℚ)/1024000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC21
#check @N11Formalization.C450Source20GroupedC21.bound
#print axioms N11Formalization.C450Source20GroupedC21.valid0
#print axioms N11Formalization.C450Source20GroupedC21.valid1
#print axioms N11Formalization.C450Source20GroupedC21.valid2
#print axioms N11Formalization.C450Source20GroupedC21.valid3
#print axioms N11Formalization.C450Source20GroupedC21.valid4
#print axioms N11Formalization.C450Source20GroupedC21.valid5
#print axioms N11Formalization.C450Source20GroupedC21.valid6
#print axioms N11Formalization.C450Source20GroupedC21.valid7
#print axioms N11Formalization.C450Source20GroupedC21.valid8
#print axioms N11Formalization.C450Source20GroupedC21.valid9
#print axioms N11Formalization.C450Source20GroupedC21.valid10
#print axioms N11Formalization.C450Source20GroupedC21.bound
#print axioms N11Formalization.C450Source20GroupedC21.endpoint_checks
