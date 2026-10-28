import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((602453123:ℚ)/1000000000),((655581697:ℚ)/1000000000),((382151041:ℚ)/1780000000),((3118745091:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3277842627:ℚ)/5000000000),((120247837144355071409052763401259764501:ℚ)/1933103194112000000000000000000000000000),((-16571411288041284509378983:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6502427963:ℚ)/10000000000),((424656073:ℚ)/625000000),((11942427963:ℚ)/55300000000),((664656073:ℚ)/2225000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((108824209:ℚ)/200000000),((3669980322238534321241837140747414394238606398617832585687:ℚ)/63159921363574218750000000000000000000000000000000000000000),((-6825123565149916740714223:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6741225797:ℚ)/10000000000),((1382761431:ℚ)/2000000000),((1353469533:ℚ)/6250000000),((921754899:ℚ)/3160000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((149994267:ℚ)/312500000),((11131324050799084702551135483353710611974870173977183:ℚ)/197215600000000000000000000000000000000000000000000000),((-71687875937820060289587607:ℚ)/295731200000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((3430295789:ℚ)/5000000000),((3516549207:ℚ)/5000000000),((559117799:ℚ)/2600000000),((1812183069:ℚ)/6250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4447705317:ℚ)/10000000000),((14458373986111536705147907614899805479236414780520057097:ℚ)/257873535156250000000000000000000000000000000000000000000),((-453416257776249812696141463:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6979936751:ℚ)/10000000000),((7152371871:ℚ)/10000000000),((12419936751:ℚ)/58150000000),((2536701201:ℚ)/8800000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4067467823:ℚ)/10000000000),((80263498085004553268045851194813777446762602581991378297197:ℚ)/1440215471200000000000000000000000000000000000000000000000000),((-1835095507132362104039720167:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1419852467:ℚ)/2000000000),((7271628391:ℚ)/10000000000),((2507852467:ℚ)/11820000000),((33334885173:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3650288437:ℚ)/10000000000),((5287123403696971787114713161875420102247060622275596203272841:ℚ)/95387534255192187500000000000000000000000000000000000000000000),((-1856488526910056063594053047:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1804642321:ℚ)/2500000000),((3695434393:ℚ)/5000000000),((3164642321:ℚ)/15012500000),((5615434393:ℚ)/19700000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3181627669:ℚ)/10000000000),((11405103313254672812669745937820611697887219134423879508524143:ℚ)/206769256135743750000000000000000000000000000000000000000000000),((-24708477342088742187020877:ℚ)/97280000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7337858491:ℚ)/10000000000),((3755046907:ℚ)/5000000000),((12777858491:ℚ)/61000000000),((17025140721:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2634100783:ℚ)/10000000000),((276576338185968380496262980748783488174184035453697945919013:ℚ)/5035918843219531250000000000000000000000000000000000000000000),((-474790734004163080874250063:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((932141349:ℚ)/1250000000),((7748500577:ℚ)/10000000000),((1612141349:ℚ)/7862500000),((34765501731:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1942049169:ℚ)/10000000000),((62142136161321096075962040779420269135616074697740374881024223:ℚ)/1122537372762500000000000000000000000000000000000000000000000000),((-831447548741237:ℚ)/3200000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((3847813883:ℚ)/5000000000),((7986853879:ℚ)/10000000000),((6567813883:ℚ)/32400000000),((2087091861:ℚ)/7400000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((304621926956614426110690218776180130933954660310564396659:ℚ)/5538905550000000000000000000000000000000000000000000000000),((-134975373:ℚ)/512000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7934065929:ℚ)/10000000000),((1978443059:ℚ)/2000000000),((13374065929:ℚ)/80000000000),((2746443059:ℚ)/8640000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((46558093267105689514640725235996434021712169561965629:ℚ)/755827200000000000000000000000000000000000000000000000),((-134975373:ℚ)/512000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9839959897:ℚ)/10000000000),((856156143:ℚ)/625000000),((15279959897:ℚ)/110400000000),((3288468429:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((29652568764911200349638847995102124273:ℚ)/396750000000000000000000000000000000000),((-134975373:ℚ)/512000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC19
#check @N11Formalization.C450Source19GroupedC19.bound
#print axioms N11Formalization.C450Source19GroupedC19.valid0
#print axioms N11Formalization.C450Source19GroupedC19.valid1
#print axioms N11Formalization.C450Source19GroupedC19.valid2
#print axioms N11Formalization.C450Source19GroupedC19.valid3
#print axioms N11Formalization.C450Source19GroupedC19.valid4
#print axioms N11Formalization.C450Source19GroupedC19.valid5
#print axioms N11Formalization.C450Source19GroupedC19.valid6
#print axioms N11Formalization.C450Source19GroupedC19.valid7
#print axioms N11Formalization.C450Source19GroupedC19.valid8
#print axioms N11Formalization.C450Source19GroupedC19.valid9
#print axioms N11Formalization.C450Source19GroupedC19.valid10
#print axioms N11Formalization.C450Source19GroupedC19.valid11
#print axioms N11Formalization.C450Source19GroupedC19.bound
#print axioms N11Formalization.C450Source19GroupedC19.endpoint_checks
