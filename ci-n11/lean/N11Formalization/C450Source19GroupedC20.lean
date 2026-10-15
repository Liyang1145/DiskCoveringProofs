import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((2990340889:ℚ)/5000000000),((1628499229:ℚ)/2500000000),((161921603:ℚ)/600000000),((2348499229:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((332487823:ℚ)/500000000),((9920524617831723008060043446671537:ℚ)/178746000000000000000000000000000000),((-1781671178462904262513713:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3229247843:ℚ)/5000000000),((270106141:ℚ)/400000000),((15127743529:ℚ)/55300000000),((385306141:ℚ)/1068000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2775933323:ℚ)/5000000000),((356102664996057322086516853496815764867606711017133661931:ℚ)/6984982023440400000000000000000000000000000000000000000000),((-47698568976403187803633:ℚ)/184832000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((1339451289:ℚ)/2000000000),((274878093:ℚ)/400000000),((6194353867:ℚ)/22500000000),((390078093:ℚ)/1106000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4923637491:ℚ)/10000000000),((1601727230990353466080639848319534376030636742431309:ℚ)/32614529850000000000000000000000000000000000000000000),((-146220511041120519081971:ℚ)/554496000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((6816604643:ℚ)/10000000000),((1747808193:ℚ)/2500000000),((31329813929:ℚ)/114400000000),((822602731:ℚ)/2343750000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2290191527:ℚ)/5000000000),((641755421248274024160441866859181894377410840023994026079:ℚ)/13163638114929199218750000000000000000000000000000000000000),((-5768988445813114688241371:ℚ)/21660000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((277437313:ℚ)/400000000),((222202993:ℚ)/312500000),((1267511939:ℚ)/4652000000),((312202993:ℚ)/893750000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2105709297:ℚ)/5000000000),((219213055506129733543847619238764611907577743690919224587:ℚ)/4526357732143020629882812500000000000000000000000000000000),((-60688552815283250722339:ℚ)/225625000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((7055241981:ℚ)/10000000000),((7229742183:ℚ)/10000000000),((32045725943:ℚ)/118200000000),((10109742183:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1904622629:ℚ)/5000000000),((71754431908776048246573984216437702097616409598092071811051:ℚ)/1490430222737377929687500000000000000000000000000000000000000),((-94129233972981372005272331:ℚ)/346560000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((3587266519:ℚ)/5000000000),((1837243197:ℚ)/2500000000),((16201799557:ℚ)/60050000000),((852414399:ℚ)/2462500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1680963653:ℚ)/5000000000),((6446666814116621609684389260913912757440562584564988993667:ℚ)/134615401130041503906250000000000000000000000000000000000000),((-5939917107958431840678611:ℚ)/21660000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((7293806863:ℚ)/10000000000),((1493637667:ℚ)/2000000000),((32761420589:ℚ)/122000000000),((2069637667:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2848229047:ℚ)/10000000000),((240046323332222508750362188991937501759529655946347273079:ℚ)/5035918843219531250000000000000000000000000000000000000000),((-1279279252208517538628977:ℚ)/4620800000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((7413064267:ℚ)/10000000000),((3853288503:ℚ)/5000000000),((33119192801:ℚ)/125800000000),((5293288503:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2222534927:ℚ)/10000000000),((105956155469526319077873264202331869361962110651389033363931:ℚ)/2192455806176757812500000000000000000000000000000000000000000),((-8494503044621697:ℚ)/30400000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((3825766407:ℚ)/5000000000),((993114161:ℚ)/1250000000),((16917299221:ℚ)/64800000000),((36570653:ℚ)/106250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6294348580612913428717515198105638625619300323171949:ℚ)/131161267089843750000000000000000000000000000000000000),((-2272797:ℚ)/8000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((1577988847:ℚ)/2000000000),((9850167879:ℚ)/10000000000),((6909966541:ℚ)/32000000000),((4243389293:ℚ)/10800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((83577306707653798601568643047747964767631362885745507:ℚ)/1476225000000000000000000000000000000000000000000000000),((-2272797:ℚ)/8000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9795670401:ℚ)/10000000000),((1707040737:ℚ)/1250000000),((40267011203:ℚ)/220800000000),((2067040737:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((884371584057596733964767257846915449:ℚ)/12398437500000000000000000000000000000),((-2272797:ℚ)/8000000)⟩
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
end N11Formalization.C450Source19GroupedC20
#check @N11Formalization.C450Source19GroupedC20.bound
#print axioms N11Formalization.C450Source19GroupedC20.valid0
#print axioms N11Formalization.C450Source19GroupedC20.valid1
#print axioms N11Formalization.C450Source19GroupedC20.valid2
#print axioms N11Formalization.C450Source19GroupedC20.valid3
#print axioms N11Formalization.C450Source19GroupedC20.valid4
#print axioms N11Formalization.C450Source19GroupedC20.valid5
#print axioms N11Formalization.C450Source19GroupedC20.valid6
#print axioms N11Formalization.C450Source19GroupedC20.valid7
#print axioms N11Formalization.C450Source19GroupedC20.valid8
#print axioms N11Formalization.C450Source19GroupedC20.valid9
#print axioms N11Formalization.C450Source19GroupedC20.valid10
#print axioms N11Formalization.C450Source19GroupedC20.valid11
#print axioms N11Formalization.C450Source19GroupedC20.bound
#print axioms N11Formalization.C450Source19GroupedC20.endpoint_checks
