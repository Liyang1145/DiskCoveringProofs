import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/16),((1:ℚ)/4),((5699999997:ℚ)/10000000000),((1510591753:ℚ)/2500000000),((38859999991:ℚ)/103000000000),((2910591753:ℚ)/6200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7227342487:ℚ)/10000000000),((-3171811321619096704337383340667162185131910522582684505699917:ℚ)/9844787315625000000000000000000000000000000000000000000000000),((-1102680636626540966012169:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((5943163451:ℚ)/10000000000),((9630797:ℚ)/15625000),((39589490353:ℚ)/104900000000),((18380797:ℚ)/40234375),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1682339537:ℚ)/2500000000),((-3077272764480458506950740277646705605588577100817022108878513:ℚ)/9567334191594531250000000000000000000000000000000000000000000),((-5604469655675710196357:ℚ)/18050000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((6064586037:ℚ)/10000000000),((6284957953:ℚ)/10000000000),((39953758111:ℚ)/106800000000),((11884957953:ℚ)/26225000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((404296117:ℚ)/625000000),((-333150579925288490737857175747507849057879106437449942999696359:ℚ)/1047260599968150000000000000000000000000000000000000000000000000),((-17986090596281676710502369:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((386619401:ℚ)/625000000),((640611583:ℚ)/1000000000),((2519858203:ℚ)/6793750000),((400203861:ℚ)/890000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3099508393:ℚ)/5000000000),((-2443250751085821727830671584236028151013958467342050502963:ℚ)/7761733359728240966796875000000000000000000000000000000000),((-180342481921619235121249:ℚ)/577600000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6307141957:ℚ)/10000000000),((1631797133:ℚ)/2500000000),((40681425871:ℚ)/110600000000),((3031797133:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1183782057:ℚ)/2000000000),((-72971473719345125654489924119246526290306831089282072963411557:ℚ)/234161650991616796875000000000000000000000000000000000000000000),((-1129924150303099259062049:ℚ)/3610000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((160707141:ℚ)/250000000),((1646923589:ℚ)/2500000000),((1026121423:ℚ)/2788750000),((3046923589:ℚ)/6912500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1406706717:ℚ)/2500000000),((-57652347620111801955714644435913380430087445621197458729:ℚ)/185059341081854629516601562500000000000000000000000000000),((-1138574619770971301099961:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((3244412997:ℚ)/5000000000),((3324090271:ℚ)/5000000000),((20613238991:ℚ)/56250000000),((6124090271:ℚ)/13943750000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((27378427:ℚ)/50000000),((-10058392748600986665668613053683933271922532225134381646521637:ℚ)/32441283783316612243652343750000000000000000000000000000000000),((-4559291838595113756877281:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((3274673047:ℚ)/5000000000),((676909603:ℚ)/1000000000),((1592616857:ℚ)/4400000000),((412303201:ℚ)/937500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5320753297:ℚ)/10000000000),((-732700300241443202391694385944295192283764560411908793:ℚ)/2395800000000000000000000000000000000000000000000000000),((-181570437323672842545769:ℚ)/577600000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((53362621:ℚ)/80000000),((21531059:ℚ)/31250000),((334167863:ℚ)/930400000),((39031059:ℚ)/89375000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4998078081:ℚ)/10000000000),((-15602808146280582213176709959735388897972048310141598143:ℚ)/51467278221444800000000000000000000000000000000000000000),((-5684618963515225501847:ℚ)/18050000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1697808561:ℚ)/2500000000),((7010712717:ℚ)/10000000000),((10533425683:ℚ)/29550000000),((12610712717:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2327653597:ℚ)/5000000000),((-910797537984323963087425335921966719935636742698575740578603:ℚ)/3029558939424902343750000000000000000000000000000000000000000),((-18220934030011201335965449:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((1728017423:ℚ)/2500000000),((7252066673:ℚ)/10000000000),((10624052269:ℚ)/30500000000),((12852066673:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4287578747:ℚ)/10000000000),((-3029050449608816240946660638148591937914374725612080436277207:ℚ)/10322936283984375000000000000000000000000000000000000000000000),((-18036222044067073537293889:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((1788385207:ℚ)/2500000000),((3867040807:ℚ)/5000000000),((10805155621:ℚ)/32400000000),((6667040807:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((861169023:ℚ)/2500000000),((-37029221040487554998548445641394703529268073670339111176743:ℚ)/131832797400000000000000000000000000000000000000000000000000),((-4704078533334811:ℚ)/15200000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7635768589:ℚ)/10000000000),((2413842393:ℚ)/2500000000),((44667305767:ℚ)/160000000000),((3813842393:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-6686371418613367181155662040791747867036058924361321210794949:ℚ)/27993600000000000000000000000000000000000000000000000000000000),((-1038319:ℚ)/3200000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((597356189:ℚ)/625000000),((13480189299:ℚ)/10000000000),((3152068567:ℚ)/13800000000),((19080189299:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1250995816940215917576304234003226272720810430426243861:ℚ)/6159543750000000000000000000000000000000000000000000000),((-1038319:ℚ)/3200000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC20
#check @N11Formalization.C450Source36GroupedC20.bound
#print axioms N11Formalization.C450Source36GroupedC20.valid0
#print axioms N11Formalization.C450Source36GroupedC20.valid1
#print axioms N11Formalization.C450Source36GroupedC20.valid2
#print axioms N11Formalization.C450Source36GroupedC20.valid3
#print axioms N11Formalization.C450Source36GroupedC20.valid4
#print axioms N11Formalization.C450Source36GroupedC20.valid5
#print axioms N11Formalization.C450Source36GroupedC20.valid6
#print axioms N11Formalization.C450Source36GroupedC20.valid7
#print axioms N11Formalization.C450Source36GroupedC20.valid8
#print axioms N11Formalization.C450Source36GroupedC20.valid9
#print axioms N11Formalization.C450Source36GroupedC20.valid10
#print axioms N11Formalization.C450Source36GroupedC20.valid11
#print axioms N11Formalization.C450Source36GroupedC20.valid12
#print axioms N11Formalization.C450Source36GroupedC20.valid13
#print axioms N11Formalization.C450Source36GroupedC20.bound
#print axioms N11Formalization.C450Source36GroupedC20.endpoint_checks
