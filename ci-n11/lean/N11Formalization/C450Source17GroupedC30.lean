import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((2816126611:ℚ)/5000000000),((6178329377:ℚ)/10000000000),((41409645943:ℚ)/53400000000),((48368305639:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7361099921:ℚ)/10000000000),((-523457223845858456526823831339496669:ℚ)/7435219921875000000000000000000000000),((-4687376845545954966600131521:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6107805109:ℚ)/10000000000),((6416144873:ℚ)/10000000000),((89001466417:ℚ)/110600000000),((50033014111:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6373784681:ℚ)/10000000000),((-1027034937745513333573594686643272475233152730404374348603:ℚ)/12683428275000000000000000000000000000000000000000000000000),((-4643864887213313654768453521:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((1586388141:ℚ)/2500000000),((6653939371:ℚ)/10000000000),((23023045833:ℚ)/28600000000),((51697575597:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2913852633:ℚ)/5000000000),((-5929796865811610414903016851936408381680520092198191481:ℚ)/73105175000000000000000000000000000000000000000000000000),((-4600281845501827619841889209:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1645820889:ℚ)/2500000000),((677282939:ℚ)/1000000000),((23795671557:ℚ)/29075000000),((5252980573:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((523206409:ℚ)/1000000000),((-1649173777722184736357286370719567676344102545013122501:ℚ)/19202120935058593750000000000000000000000000000000000000),((-45784635563001445590655129:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((837767923:ℚ)/1250000000),((68917149:ℚ)/100000000),((12090982999:ℚ)/14775000000),((533620043:ℚ)/581500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((982003479:ℚ)/2000000000),((-648933683244411821472353920457574735264884661871430701:ℚ)/7559511877441406250000000000000000000000000000000000000),((-1366988210227345796057947:ℚ)/4435968000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1705249919:ℚ)/2500000000),((1402119223:ℚ)/2000000000),((24568248947:ℚ)/30025000000),((10838834561:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2283643847:ℚ)/5000000000),((-21773419054837473295915996990778341757241274501410905153:ℚ)/253758339990234375000000000000000000000000000000000000000),((-181390929665951983425475921:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((34699263:ℚ)/50000000),((282801407:ℚ)/400000000),((55454491:ℚ)/67250000),((2184409849:ℚ)/2402000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((167951377:ℚ)/400000000),((-83677648271140386366010718425908859908504747987:ℚ)/950444775390625000000000000000000000000000000000),((-7238143106309399474352001:ℚ)/23658496000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((6999277849:ℚ)/10000000000),((7129473237:ℚ)/10000000000),((100590612037:ℚ)/122000000000),((55026312659:ℚ)/60525000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4002653957:ℚ)/10000000000),((-499353324446978988816422663765495605205215904599361083741:ℚ)/5674525000000000000000000000000000000000000000000000000000),((-13538703431462819696054246443:ℚ)/44359680000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1411740463:ℚ)/2000000000),((7248346453:ℚ)/10000000000),((20272626019:ℚ)/24780000000),((55858425171:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((759395951:ℚ)/2000000000),((-339709824269291937390579379274668918798467838625828161:ℚ)/3962531081250000000000000000000000000000000000000000000),((-4491011041424806556109376441:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((7177548967:ℚ)/10000000000),((7367215943:ℚ)/10000000000),((102908136571:ℚ)/125800000000),((56690511601:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3349877479:ℚ)/10000000000),((-520662177768531200490015668344310615168149183262577403:ℚ)/6075639379882812500000000000000000000000000000000000000),((-4469102903117104279343812401:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((7296392697:ℚ)/10000000000),((1520988879:ℚ)/2000000000),((34817701687:ℚ)/43200000000),((11670922153:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((283609513:ℚ)/1000000000),((-84542179787291178284955645486042256167446552621262493:ℚ)/1036800000000000000000000000000000000000000000000000000),((-306519779:ℚ)/1024000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((3767035951:ℚ)/5000000000),((9506380943:ℚ)/10000000000),((53771467363:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1318129033:ℚ)/10000000000),((-12363134989626698468285270916827622079196187777452422033:ℚ)/300000000000000000000000000000000000000000000000000000000),((-306519779:ℚ)/1024000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((1887039769:ℚ)/2000000000),((6654033273:ℚ)/5000000000),((26451516997:ℚ)/44160000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-198607431491884700885860352664180767:ℚ)/10764582912000000000000000000000000000),((-306519779:ℚ)/1024000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
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
    CellBound source17 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC30
#check @N11Formalization.C450Source17GroupedC30.bound
#print axioms N11Formalization.C450Source17GroupedC30.valid0
#print axioms N11Formalization.C450Source17GroupedC30.valid1
#print axioms N11Formalization.C450Source17GroupedC30.valid2
#print axioms N11Formalization.C450Source17GroupedC30.valid3
#print axioms N11Formalization.C450Source17GroupedC30.valid4
#print axioms N11Formalization.C450Source17GroupedC30.valid5
#print axioms N11Formalization.C450Source17GroupedC30.valid6
#print axioms N11Formalization.C450Source17GroupedC30.valid7
#print axioms N11Formalization.C450Source17GroupedC30.valid8
#print axioms N11Formalization.C450Source17GroupedC30.valid9
#print axioms N11Formalization.C450Source17GroupedC30.valid10
#print axioms N11Formalization.C450Source17GroupedC30.valid11
#print axioms N11Formalization.C450Source17GroupedC30.valid12
#print axioms N11Formalization.C450Source17GroupedC30.bound
#print axioms N11Formalization.C450Source17GroupedC30.endpoint_checks
