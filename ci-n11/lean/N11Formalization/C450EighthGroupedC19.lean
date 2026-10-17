import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((6141396691:ℚ)/10000000000),((6640751459:ℚ)/10000000000),((8061396691:ℚ)/53400000000),((24402254377:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6299134227:ℚ)/10000000000),((190004460808219390041162851674495089912203:ℚ)/17397928747008000000000000000000000000000000),((-91395944775275780318926961:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((206775981:ℚ)/312500000),((6878397519:ℚ)/10000000000),((266775981:ℚ)/1728125000),((25115192557:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2571515999:ℚ)/5000000000),((71725010267487201542537149590498806374747403529745098918867367:ℚ)/6984982023440400000000000000000000000000000000000000000000000000),((-278058809933045985020723:ℚ)/5415000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6854526311:ℚ)/10000000000),((3498608423:ℚ)/5000000000),((8774526311:ℚ)/56250000000),((12735825269:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4466218127:ℚ)/10000000000),((122304040429731015776559097592049909295897247182158884171:ℚ)/12230448693750000000000000000000000000000000000000000000000),((-96673466932104697314745401:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((6973368827:ℚ)/10000000000),((7056625637:ℚ)/10000000000),((8893368827:ℚ)/56725000000),((25649876911:ℚ)/112500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2044628371:ℚ)/5000000000),((452567214336517212537789756546863008398559931581671915950034023:ℚ)/45814882434082031250000000000000000000000000000000000000000000000),((-97556166962821843512201249:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((3516394461:ℚ)/5000000000),((1779008467:ℚ)/2500000000),((406944951:ℚ)/2600000000),((6457025401:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3887938181:ℚ)/10000000000),((56157260625529766093699295496579671098751314124220793:ℚ)/5703921439941406250000000000000000000000000000000000000),((-73498388763751888220303603:ℚ)/1386240000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((7092208267:ℚ)/10000000000),((143508831:ℚ)/200000000),((9012208267:ℚ)/57675000000),((520126493:ℚ)/2288000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3676201413:ℚ)/10000000000),((325844445417543806633229043820603596160305004094527152087:ℚ)/33201829933958400000000000000000000000000000000000000000000),((-98439759721573335987617409:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((11174417:ℚ)/15625000),((3617424349:ℚ)/5000000000),((14174417:ℚ)/90859375),((13092273047:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1726062911:ℚ)/5000000000),((211574869120109782382374102357927971768294360652041127384973:ℚ)/21624246980104253906250000000000000000000000000000000000000000),((-241410867182224267009:ℚ)/4512500000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/8),((3:ℚ)/16),((360552239:ℚ)/500000000),((1823563831:ℚ)/2500000000),((456552239:ℚ)/2931250000),((6590691493:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3213126599:ℚ)/10000000000),((247230306886313559167172790175883600025752115109479190737303:ℚ)/25342306337978540039062500000000000000000000000000000000000000),((-248310615617071598541801:ℚ)/4620800000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1454092397:ℚ)/2000000000),((3676830721:ℚ)/5000000000),((1838092397:ℚ)/11820000000),((13270492163:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((738895221:ℚ)/2500000000),((1069764455222173536971805209656402672958446753204609860690091:ℚ)/109962234134609985351562500000000000000000000000000000000000000),((-3990672999776531504345329:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((732987851:ℚ)/1000000000),((7413067063:ℚ)/10000000000),((924987851:ℚ)/5957500000),((26719201189:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2674130233:ℚ)/10000000000),((1706046501431425852353520334197975775623040484557632875069158311:ℚ)/175833567001787850000000000000000000000000000000000000000000000000),((-1002096275443783289953281:ℚ)/18483200000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1847323593:ℚ)/2500000000),((7472472199:ℚ)/10000000000),((2327323593:ℚ)/15012500000),((26897416597:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2360232519:ℚ)/10000000000),((9223931523538570814887034171939726136735927591875631679355181:ℚ)/953077439830306982421875000000000000000000000000000000000000000),((-18872372627935664802357707:ℚ)/346560000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7448709587:ℚ)/10000000000),((7591281063:ℚ)/10000000000),((9368709587:ℚ)/61000000000),((27253843189:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1998651139:ℚ)/10000000000),((390822691216116666295948633403850784865876066200729806939733:ℚ)/40287350745756250000000000000000000000000000000000000000000000),((-101095904519981920964287089:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((7567538137:ℚ)/10000000000),((4033249623:ℚ)/5000000000),((9487538137:ℚ)/64800000000),((14339748869:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((57786933:ℚ)/625000000),((23072858221476185026596398671991666988502513407421456368293:ℚ)/2326909907812500000000000000000000000000000000000000000000000),((-101983078053526856765423289:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((2010707321:ℚ)/2500000000),((9967164601:ℚ)/10000000000),((2490707321:ℚ)/20000000000),((34381493803:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((26972393904416659228544972823405143103874512470802958633:ℚ)/2550916800000000000000000000000000000000000000000000000000),((-1415867:ℚ)/25600000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((4971858547:ℚ)/5000000000),((6883972751:ℚ)/5000000000),((5931858547:ℚ)/55200000000),((22891918253:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((7595349971558246248827843682119370448543:ℚ)/609408000000000000000000000000000000000000),((-1415867:ℚ)/25600000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC19
#check @N11Formalization.C450EighthGroupedC19.bound
#print axioms N11Formalization.C450EighthGroupedC19.valid0
#print axioms N11Formalization.C450EighthGroupedC19.valid1
#print axioms N11Formalization.C450EighthGroupedC19.valid2
#print axioms N11Formalization.C450EighthGroupedC19.valid3
#print axioms N11Formalization.C450EighthGroupedC19.valid4
#print axioms N11Formalization.C450EighthGroupedC19.valid5
#print axioms N11Formalization.C450EighthGroupedC19.valid6
#print axioms N11Formalization.C450EighthGroupedC19.valid7
#print axioms N11Formalization.C450EighthGroupedC19.valid8
#print axioms N11Formalization.C450EighthGroupedC19.valid9
#print axioms N11Formalization.C450EighthGroupedC19.valid10
#print axioms N11Formalization.C450EighthGroupedC19.valid11
#print axioms N11Formalization.C450EighthGroupedC19.valid12
#print axioms N11Formalization.C450EighthGroupedC19.valid13
#print axioms N11Formalization.C450EighthGroupedC19.valid14
#print axioms N11Formalization.C450EighthGroupedC19.bound
#print axioms N11Formalization.C450EighthGroupedC19.endpoint_checks
