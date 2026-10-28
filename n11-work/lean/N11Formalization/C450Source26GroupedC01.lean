import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((443187091:ℚ)/625000000),((3629687501:ℚ)/5000000000),(-1:ℚ),((-1129561273:ℚ)/1251875000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((1840323207:ℚ)/5000000000),((108711880694642746142604297265853:ℚ)/313438203125000000000000000000000),((79742800613124887208723:ℚ)/72200000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((161:ℚ)/256),(-1:ℚ),((-15:ℚ)/16),((1787613503:ℚ)/2500000000),((3644531251:ℚ)/5000000000),(-1:ℚ),((-4562840509:ℚ)/5031250000),((4973408481:ℚ)/5000000000),((62276473:ℚ)/62500000),((128974617:ℚ)/1250000000),((1728341701:ℚ)/5000000000),((21757381963989549906927521341108951:ℚ)/63283691406250000000000000000000000),((79898570221640687208723:ℚ)/72200000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((2003:ℚ)/3200) ((161:ℚ)/256) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((161:ℚ)/256),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7180183683:ℚ)/10000000000),((7318750003:ℚ)/10000000000),(-1:ℚ),((-18340551049:ℚ)/20220000000),((9929701407:ℚ)/10000000000),((9946816967:ℚ)/10000000000),((18538009:ℚ)/156250000),((3339316509:ℚ)/10000000000),((234116980733556844134396809312982779:ℚ)/681414000000000000000000000000000000),((320218046205255329503507:ℚ)/288800000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((161:ℚ)/256) ((1011:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7209912957:ℚ)/10000000000),((3674218751:ℚ)/5000000000),(-1:ℚ),((-18429738871:ℚ)/20315000000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((3217838851:ℚ)/10000000000),((354248212554714972550238256557938949:ℚ)/1031748062500000000000000000000000000),((80210624586377365333723:ℚ)/72200000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((90495523:ℚ)/125000000),((3689062501:ℚ)/5000000000),(-1:ℚ),((-231486569:ℚ)/255125000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((1545882667:ℚ)/5000000000),((3171624277758714585681347905063:ℚ)/9243375000000000000000000000000),((80366909342598243458723:ℚ)/72200000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7269370337:ℚ)/10000000000),((3703906251:ℚ)/5000000000),(-1:ℚ),((-18608111011:ℚ)/20505000000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((2960508267:ℚ)/10000000000),((40048870994472126868880940625781841:ℚ)/116793062500000000000000000000000000),((241570097444162442876169:ℚ)/216600000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((1824774613:ℚ)/2500000000),((3718750001:ℚ)/5000000000),(-1:ℚ),((-4674323839:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((352918021:ℚ)/1250000000),((45444840426845129423811636351190101:ℚ)/132612500000000000000000000000000000),((80679994002745077833723:ℚ)/72200000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7328826193:ℚ)/10000000000),((3733593751:ℚ)/5000000000),(-1:ℚ),((-18786478579:ℚ)/20695000000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((2679365323:ℚ)/10000000000),((73338597667778889523051382823767759:ℚ)/214141512500000000000000000000000000),((80836793906671034083723:ℚ)/72200000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7358553563:ℚ)/10000000000),((3748437501:ℚ)/5000000000),(-1:ℚ),((-18875660689:ℚ)/20790000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((1263703333:ℚ)/5000000000),((5870517997303391056799962706521577:ℚ)/17151750000000000000000000000000000),((242981296579496049126169:ℚ)/216600000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((923535071:ℚ)/1250000000),((3778125001:ℚ)/5000000000),(-1:ℚ),((-2370605213:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((591482593:ℚ)/2500000000),((2961229521597802113811872718293069:ℚ)/8596882812500000000000000000000000),((81308223913859059083723:ℚ)/72200000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((7447733503:ℚ)/10000000000),((3837500001:ℚ)/5000000000),(-1:ℚ),((-19143200509:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((501277441:ℚ)/2500000000),((397653420069546450231564209752697851:ℚ)/1140624000000000000000000000000000000),((141171:ℚ)/125000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((3783317603:ℚ)/5000000000),((8150000003:ℚ)/10000000000),(-1:ℚ),((-9749952809:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),((937370837:ℚ)/10000000000),((730073407298149184891048629308302953:ℚ)/1963104000000000000000000000000000000),((141171:ℚ)/125000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((4021095769:ℚ)/5000000000),((4550000001:ℚ)/5000000000),(-1:ℚ),((-10463287307:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((328767361879475028286754118388482161:ℚ)/839808000000000000000000000000000000),((141171:ℚ)/125000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((8993108177:ℚ)/10000000000),((5500000001:ℚ)/5000000000),(-1:ℚ),((-23779324531:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6392828608765716497198380170138564433:ℚ)/15360000000000000000000000000000000000),((141171:ℚ)/125000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((272360461:ℚ)/250000000),((14800000003:ℚ)/10000000000),(-1:ℚ),((-737081383:ℚ)/1104000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((280034823014972954773199:ℚ)/609408000000000000000000),((141171:ℚ)/125000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source26 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC01
#check @N11Formalization.C450Source26GroupedC01.bound
#print axioms N11Formalization.C450Source26GroupedC01.valid0
#print axioms N11Formalization.C450Source26GroupedC01.valid1
#print axioms N11Formalization.C450Source26GroupedC01.valid2
#print axioms N11Formalization.C450Source26GroupedC01.valid3
#print axioms N11Formalization.C450Source26GroupedC01.valid4
#print axioms N11Formalization.C450Source26GroupedC01.valid5
#print axioms N11Formalization.C450Source26GroupedC01.valid6
#print axioms N11Formalization.C450Source26GroupedC01.valid7
#print axioms N11Formalization.C450Source26GroupedC01.valid8
#print axioms N11Formalization.C450Source26GroupedC01.valid9
#print axioms N11Formalization.C450Source26GroupedC01.valid10
#print axioms N11Formalization.C450Source26GroupedC01.valid11
#print axioms N11Formalization.C450Source26GroupedC01.valid12
#print axioms N11Formalization.C450Source26GroupedC01.valid13
#print axioms N11Formalization.C450Source26GroupedC01.valid14
#print axioms N11Formalization.C450Source26GroupedC01.bound
#print axioms N11Formalization.C450Source26GroupedC01.endpoint_checks
