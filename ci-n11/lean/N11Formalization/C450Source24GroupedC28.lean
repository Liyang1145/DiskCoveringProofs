import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5480064827:ℚ)/10000000000),((6039339699:ℚ)/10000000000),((74360713097:ℚ)/106800000000),((21798019097:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1913659211:ℚ)/2500000000),((-27051915843565650792925179031880219071:ℚ)/152273304000000000000000000000000000000),((-645369684940859786112597851:ℚ)/1774387200000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((5957204297:ℚ)/10000000000),((6277897739:ℚ)/10000000000),((79609247267:ℚ)/110600000000),((22513693217:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3349830873:ℚ)/5000000000),((-365812966666969125450238774301102833141254267854847916427:ℚ)/1811918325000000000000000000000000000000000000000000000000),((-212617916165742092134706457:ℚ)/591462400000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((1548915773:ℚ)/2500000000),((799643723:ℚ)/1250000000),((20558073503:ℚ)/28125000000),((2858931169:ℚ)/3456250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6176893913:ℚ)/10000000000),((-4940248625648197078626549460595363324077014280382259721:ℚ)/23174285888671875000000000000000000000000000000000000000),((-3302217090274817438051993:ℚ)/9241600000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6314868059:ℚ)/10000000000),((130327701:ℚ)/200000000),((7594868059:ℚ)/10400000000),((464583103:ℚ)/562500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2950332387:ℚ)/5000000000),((-748324387820137414884798124357954499826889106860649471:ℚ)/3515200000000000000000000000000000000000000000000000000),((-252060348276606162992651:ℚ)/709754880000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((643405783:ℚ)/1000000000),((6635604367:ℚ)/10000000000),((8485463613:ℚ)/11630000000),((23586813101:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5612573463:ℚ)/10000000000),((-261252520532243318324188000808295491280716324480688577:ℚ)/1228935739843750000000000000000000000000000000000000000),((-208743103022217698512445313:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((3276616577:ℚ)/5000000000),((209225259:ℚ)/312500000),((43082782347:ℚ)/58625000000),((742675777:ℚ)/908593750),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5310663193:ℚ)/10000000000),((-4897665060035255611977937476242066600653524244114045281:ℚ)/22487467956542968750000000000000000000000000000000000000),((-609620111778790338184331:ℚ)/1732800000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((330640781:ℚ)/500000000),((6754808509:ℚ)/10000000000),((1447016197:ℚ)/1970000000),((23944425527:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5153763031:ℚ)/10000000000),((-1299617640431701796338697616338934728203096006307217:ℚ)/5972947656250000000000000000000000000000000000000000),((-207420329835937411595956777:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3336197367:ℚ)/5000000000),((3407202559:ℚ)/5000000000),((43738171037:ℚ)/59575000000),((12061607677:ℚ)/14775000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((199695997:ℚ)/400000000),((-430893445598594591752443211556641529141180769241272113579:ℚ)/1982272835009765625000000000000000000000000000000000000000),((-51688274453438138181788577:ℚ)/147865600000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((420748161:ℚ)/625000000),((3436999101:ℚ)/5000000000),((5508229771:ℚ)/7506250000),((12150997303:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((4826122783:ℚ)/10000000000),((-17938504028431888497248284085336698588930929495986511:ℚ)/82603626298904418945312500000000000000000000000000000),((-154561476365354855802595451:ℚ)/443596800000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((271661729:ℚ)/400000000),((55945393:ℚ)/80000000),((3551479019:ℚ)/4880000000),((197276179:ℚ)/240200000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((29090009:ℚ)/62500000),((-76873494161854123596585419252292009168514471035716399:ℚ)/363169600000000000000000000000000000000000000000000000),((-13102593084414079327233:ℚ)/37853593600000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6910679243:ℚ)/10000000000),((3556168459:ℚ)/5000000000),((90097471673:ℚ)/123900000000),((12508505377:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2145988647:ℚ)/5000000000),((-4985348369600777895738258221491216379839517489994938779:ℚ)/23586494531250000000000000000000000000000000000000000000),((-140829967635682030929457:ℚ)/409600000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((7029803367:ℚ)/10000000000),((3615743589:ℚ)/5000000000),((91407837037:ℚ)/125800000000),((12687230767:ℚ)/15487500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((779657639:ℚ)/2000000000),((-1282277242738703230039567927215552128427845362710079697:ℚ)/6075639379882812500000000000000000000000000000000000000),((-151480001757355564009208171:ℚ)/443596800000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((3574458069:ℚ)/5000000000),((7469752321:ℚ)/10000000000),((46359038759:ℚ)/64800000000),((26089256963:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((865662653:ℚ)/2500000000),((-6334492865468881127513416900258729410276462017047198633:ℚ)/31492800000000000000000000000000000000000000000000000000),((-551679423994973568832377:ℚ)/1638400000000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7387109629:ℚ)/10000000000),((2343640091:ℚ)/2500000000),((95338205919:ℚ)/160000000000),((7950920273:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1186247327:ℚ)/5000000000),((-83518031425106074596737475063236270185914765431554695771:ℚ)/800000000000000000000000000000000000000000000000000000000),((-342087467:ℚ)/1024000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((371658713:ℚ)/400000000),((6590097933:ℚ)/5000000000),((4651445843:ℚ)/8832000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-3656280495765761147326228342700989:ℚ)/86116663296000000000000000000000000),((-342087467:ℚ)/1024000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC28
#check @N11Formalization.C450Source24GroupedC28.bound
#print axioms N11Formalization.C450Source24GroupedC28.valid0
#print axioms N11Formalization.C450Source24GroupedC28.valid1
#print axioms N11Formalization.C450Source24GroupedC28.valid2
#print axioms N11Formalization.C450Source24GroupedC28.valid3
#print axioms N11Formalization.C450Source24GroupedC28.valid4
#print axioms N11Formalization.C450Source24GroupedC28.valid5
#print axioms N11Formalization.C450Source24GroupedC28.valid6
#print axioms N11Formalization.C450Source24GroupedC28.valid7
#print axioms N11Formalization.C450Source24GroupedC28.valid8
#print axioms N11Formalization.C450Source24GroupedC28.valid9
#print axioms N11Formalization.C450Source24GroupedC28.valid10
#print axioms N11Formalization.C450Source24GroupedC28.valid11
#print axioms N11Formalization.C450Source24GroupedC28.valid12
#print axioms N11Formalization.C450Source24GroupedC28.valid13
#print axioms N11Formalization.C450Source24GroupedC28.valid14
#print axioms N11Formalization.C450Source24GroupedC28.bound
#print axioms N11Formalization.C450Source24GroupedC28.endpoint_checks
