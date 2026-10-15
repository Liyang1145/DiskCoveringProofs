import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1410845771:ℚ)/2000000000),((3609687501:ℚ)/5000000000),(-1:ℚ),((-3618137313:ℚ)/4006000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((1906414641:ℚ)/5000000000),((61338465393844358713165171308887:ℚ)/200600450000000000000000000000000),((2290282980274482096887131:ℚ)/2166000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((161:ℚ)/256),(-1:ℚ),((-15:ℚ)/16),((7113682417:ℚ)/10000000000),((3624531251:ℚ)/5000000000),(-1:ℚ),((-2609863893:ℚ)/2875000000),((4973408481:ℚ)/5000000000),((62276473:ℚ)/62500000),((128974617:ℚ)/1250000000),((899190477:ℚ)/2500000000),((390899186932623669687913124250981:ℚ)/1291503906250000000000000000000000),((764970762892517398962377:ℚ)/722000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((2003:ℚ)/3200) ((161:ℚ)/256) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((161:ℚ)/256),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1395197:ℚ)/1953125),((7278750003:ℚ)/10000000000),(-1:ℚ),((-4780788:ℚ)/5265625),((9929701407:ℚ)/10000000000),((9946816967:ℚ)/10000000000),((18538009:ℚ)/156250000),((1741970083:ℚ)/5000000000),((21472779544247382704368382288139:ℚ)/70980625000000000000000000000000),((9198187772204143937609179:ℚ)/8664000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((161:ℚ)/256) ((1011:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7173134499:ℚ)/10000000000),((3654218751:ℚ)/5000000000),(-1:ℚ),((-18447403497:ℚ)/20315000000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((1683750471:ℚ)/5000000000),((19497785846562728867451893432260139:ℚ)/64484253906250000000000000000000000),((2304186942926319350012131:ℚ)/2166000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3601429999:ℚ)/5000000000),((3669062501:ℚ)/5000000000),(-1:ℚ),((-9268289997:ℚ)/10205000000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((1623527269:ℚ)/5000000000),((23279186360018497515197010773079:ℚ)/77028125000000000000000000000000),((769610762924005467712377:ℚ)/722000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2041:ℚ)/3200),((8183:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7232585143:ℚ)/10000000000),((459560547:ℚ)/625000000),(-1:ℚ),((-18625755429:ℚ)/20457500000),((9888211123:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((37416203:ℚ)/250000000),((3122136639:ℚ)/10000000000),((917287376411502468017830320703317:ℚ)/3050359375000000000000000000000000),((36111827599612395294379:ℚ)/33843750000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8183:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((8183:ℚ)/12800),((4101:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((226482737:ℚ)/312500000),((3683906251:ℚ)/5000000000),(-1:ℚ),((-194482737:ℚ)/213593750),((4940065779:ℚ)/5000000000),((1236026391:ℚ)/1250000000),((774947369:ℚ)/5000000000),((382228777:ℚ)/1250000000),((137162096366868312444637170841411:ℚ)/456222900390625000000000000000000),((771160993477307480212377:ℚ)/722000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((8183:ℚ)/12800) ((4101:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7262309939:ℚ)/10000000000),((1845664063:ℚ)/2500000000),(-1:ℚ),((-18714929817:ℚ)/20552500000),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((2992186671:ℚ)/10000000000),((317416730483471057100631486675666323:ℚ)/1056013140625000000000000000000000000),((192984194245183652377313:ℚ)/180500000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((7277172207:ℚ)/10000000000),((3698750001:ℚ)/5000000000),(-1:ℚ),((-18759516621:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((585023183:ℚ)/2000000000),((39851918845047143414771675945546919:ℚ)/132612500000000000000000000000000000),((2318139017906037462512131:ℚ)/2166000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((729203439:ℚ)/1000000000),((3713593751:ℚ)/5000000000),(-1:ℚ),((-1880410317:ℚ)/2069500000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((571303467:ℚ)/2000000000),((40390683988473194932282546143309:ℚ)/133838445312500000000000000000000),((774266800398120489587377:ℚ)/722000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7321758501:ℚ)/10000000000),((3728437501:ℚ)/5000000000),(-1:ℚ),((-6297758501:ℚ)/6930000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((339283811:ℚ)/1250000000),((641592137918387880419056816253:ℚ)/2126953125000000000000000000000),((775822376765631486462377:ℚ)/722000000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1837870569:ℚ)/2500000000),((3743281251:ℚ)/5000000000),(-1:ℚ),((-4745611707:ℚ)/5221250000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((2564351101:ℚ)/10000000000),((82196661087860692279773860384747059:ℚ)/272614515625000000000000000000000000),((2332139205213636434387131:ℚ)/2166000000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((3690602861:ℚ)/5000000000),((3758125001:ℚ)/5000000000),(-1:ℚ),((-9535808583:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2405324217:ℚ)/10000000000),((2590917084655384552088146707501971:ℚ)/8596882812500000000000000000000000),((778938875314862464587377:ℚ)/722000000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7410928841:ℚ)/10000000000),((3787812501:ℚ)/5000000000),(-1:ℚ),((-19160786523:ℚ)/21170000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((279405757:ℚ)/1250000000),((42551257736102865654394932245591239:ℚ)/140052781250000000000000000000000000),((2346187504849116265637131:ℚ)/2166000000000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((3735187059:ℚ)/5000000000),((3817500001:ℚ)/5000000000),(-1:ℚ),((-3223187059:ℚ)/3560000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1849580689:ℚ)/10000000000),((601073595856785431087396565196289:ℚ)/1980250000000000000000000000000000),((135621:ℚ)/125000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((7529818143:ℚ)/10000000000),((3936250001:ℚ)/5000000000),(-1:ℚ),((-19517454429:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((170006457:ℚ)/1250000000),((123850361160822895565976627833923:ℚ)/390062500000000000000000000000000),((135621:ℚ)/125000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((1553516473:ℚ)/2000000000),((8110000003:ℚ)/10000000000),(-1:ℚ),((-311242263:ℚ)/352000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((12229402396364393915619046292761:ℚ)/38720000000000000000000000000000),((135621:ℚ)/125000)⟩
theorem valid16 : Valid source25 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((4002664503:ℚ)/5000000000),((4530000001:ℚ)/5000000000),(-1:ℚ),((-3490664503:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2082049649407329392445440756973739:ℚ)/5832000000000000000000000000000000),((135621:ℚ)/125000)⟩
theorem valid17 : Valid source25 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((35824683:ℚ)/40000000),((5480000001:ℚ)/5000000000),(-1:ℚ),((-95186049:ℚ)/128000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1972323853783996224272338056089:ℚ)/5120000000000000000000000000000),((135621:ℚ)/125000)⟩
theorem valid18 : Valid source25 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((2714343499:ℚ)/2500000000),((14760000003:ℚ)/10000000000),(-1:ℚ),((-2458343499:ℚ)/3680000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((181535808014901291076549:ℚ)/423200000000000000000000),((135621:ℚ)/125000)⟩
theorem valid19 : Valid source25 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((161:ℚ)/256) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source25 nn0 nn1 Qcell ((161:ℚ)/256) ((2041:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source25 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source25 nn0 nn1 Qcell ((8221:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source25 nn0 nn1 Qcell ((4101:ℚ)/6400) ((4139:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source25 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4139:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((4139:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((4139:ℚ)/6400) ((4177:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source25 nn0 nn1 Qcell ((4177:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source25 nn0 nn1 Qcell ((4139:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source25 nn0 nn1 Qcell ((4139:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC01
#check @N11Formalization.C450Source25GroupedC01.bound
#print axioms N11Formalization.C450Source25GroupedC01.valid0
#print axioms N11Formalization.C450Source25GroupedC01.valid1
#print axioms N11Formalization.C450Source25GroupedC01.valid2
#print axioms N11Formalization.C450Source25GroupedC01.valid3
#print axioms N11Formalization.C450Source25GroupedC01.valid4
#print axioms N11Formalization.C450Source25GroupedC01.valid5
#print axioms N11Formalization.C450Source25GroupedC01.valid6
#print axioms N11Formalization.C450Source25GroupedC01.valid7
#print axioms N11Formalization.C450Source25GroupedC01.valid8
#print axioms N11Formalization.C450Source25GroupedC01.valid9
#print axioms N11Formalization.C450Source25GroupedC01.valid10
#print axioms N11Formalization.C450Source25GroupedC01.valid11
#print axioms N11Formalization.C450Source25GroupedC01.valid12
#print axioms N11Formalization.C450Source25GroupedC01.valid13
#print axioms N11Formalization.C450Source25GroupedC01.valid14
#print axioms N11Formalization.C450Source25GroupedC01.valid15
#print axioms N11Formalization.C450Source25GroupedC01.valid16
#print axioms N11Formalization.C450Source25GroupedC01.valid17
#print axioms N11Formalization.C450Source25GroupedC01.valid18
#print axioms N11Formalization.C450Source25GroupedC01.valid19
#print axioms N11Formalization.C450Source25GroupedC01.bound
#print axioms N11Formalization.C450Source25GroupedC01.endpoint_checks
