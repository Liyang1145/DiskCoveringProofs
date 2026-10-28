import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((156685441:ℚ)/250000000),((3270350693:ℚ)/5000000000),((-2390350693:ℚ)/12400000000),((-278056323:ℚ)/2575000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6011951103:ℚ)/10000000000),((28552093024686499420526314623484815156178416489018613:ℚ)/661612050781250000000000000000000000000000000000000000),((269507688092066240298293:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6505475359:ℚ)/10000000000),((677880057:ℚ)/1000000000),((-501880057:ℚ)/2575000000),((-3945475359:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((54334597:ℚ)/100000000),((62150097447785647649587137379829634182410350204982767993:ℚ)/1452236140000000000000000000000000000000000000000000000000),((9288886468695720849293:ℚ)/577600000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6743493261:ℚ)/10000000000),((1724458599:ℚ)/2500000000),((-1284458599:ℚ)/6675000000),((-12550479783:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((479335141:ℚ)/1000000000),((18033864275658261975867886015600792529133186680972194520981:ℚ)/428656986626250000000000000000000000000000000000000000000000),((48643436197900849085557:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((686248859:ℚ)/1000000000),((1754214609:ℚ)/2500000000),((-1314214609:ℚ)/6793750000),((-1290746577:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((888380071:ℚ)/2000000000),((1204720169673609908629169415273247824185505986640986911:ℚ)/28722680281093750000000000000000000000000000000000000000),((43988301919800793647117:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1396295093:ℚ)/2000000000),((7076366943:ℚ)/10000000000),((-5316366943:ℚ)/27650000000),((-2652885279:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((406234723:ℚ)/1000000000),((19968769887356296977644328420671274555471720694221594367:ℚ)/479748772829921875000000000000000000000000000000000000000),((628553723480202139143293:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((1760241467:ℚ)/2500000000),((7135873189:ℚ)/10000000000),((-5375873189:ℚ)/27887500000),((-1120241467:ℚ)/9375000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3859456329:ℚ)/10000000000),((1119416412168808181723204883012150189914506307844032431:ℚ)/26928037405014038085937500000000000000000000000000000000),((591334158809181601442997:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1775113579:ℚ)/2500000000),((7195377229:ℚ)/10000000000),((-5435377229:ℚ)/28125000000),((-3405340737:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((72917847:ℚ)/200000000),((26643151164118562280974154068337311538814651893591577:ℚ)/641691161993408203125000000000000000000000000000000000),((554122590941526614548037:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((3579970429:ℚ)/5000000000),((7254879119:ℚ)/10000000000),((-5494879119:ℚ)/28362500000),((-6899911287:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3419651863:ℚ)/10000000000),((22013399191622879308947234045202589205326764135285079040523:ℚ)/530802054640000000000000000000000000000000000000000000000000),((516918988578132320866077:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((902428193:ℚ)/1250000000),((228574341:ℚ)/312500000),((-173574341:ℚ)/893750000),((-582428193:ℚ)/4806250000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((397253013:ℚ)/1250000000),((2919468495655098466076421114556408286940537678161:ℚ)/70474575960636138916015625000000000000000000000000),((234239902228607305021:ℚ)/28203125000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((7278908417:ℚ)/10000000000),((368693833:ℚ)/500000000),((-93564611:ℚ)/480625000),((-14156725251:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2917183069:ℚ)/10000000000),((62572697168037478912433390969559571543501427789376231445339:ℚ)/1512082534303750000000000000000000000000000000000000000000000),((1106338892574122542773:ℚ)/144400000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7338389523:ℚ)/10000000000),((7492866219:ℚ)/10000000000),((-5732866219:ℚ)/29075000000),((-4778389523:ℚ)/39400000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2631415903:ℚ)/10000000000),((923145126596904362838891627048388865167269681275101101089:ℚ)/22228921997500000000000000000000000000000000000000000000000),((406205504921420957654677:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((3728673303:ℚ)/5000000000),((966352861:ℚ)/1250000000),((-248784287:ℚ)/1231250000),((-7346019909:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1940577189:ℚ)/10000000000),((2337020081575262480737184218348457855466861725711300488537:ℚ)/55894071250000000000000000000000000000000000000000000000000),((174584349817633:ℚ)/30400000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((7695241373:ℚ)/10000000000),((8206655677:ℚ)/10000000000),((-6446655677:ℚ)/30500000000),((-5135241373:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((86751660821087631944557781830054412129607771666272039411:ℚ)/2049131520000000000000000000000000000000000000000000000000),((33313:ℚ)/8000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((81709613:ℚ)/100000000),((2527298541:ℚ)/2500000000),((-2087298541:ℚ)/8100000000),((-168328839:ℚ)/1600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((18884557343529171192316467221028813890474848805237831:ℚ)/414720000000000000000000000000000000000000000000000000),((33313:ℚ)/8000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((1259144493:ℚ)/1250000000),((2782434339:ℚ)/2000000000),((-2430434339:ℚ)/8000000000),((-939144493:ℚ)/9200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((37102188344334353277000209079415066743074912635245479:ℚ)/730020000000000000000000000000000000000000000000000000),((33313:ℚ)/8000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC13
#check @N11Formalization.C450Source13GroupedC13.bound
#print axioms N11Formalization.C450Source13GroupedC13.valid0
#print axioms N11Formalization.C450Source13GroupedC13.valid1
#print axioms N11Formalization.C450Source13GroupedC13.valid2
#print axioms N11Formalization.C450Source13GroupedC13.valid3
#print axioms N11Formalization.C450Source13GroupedC13.valid4
#print axioms N11Formalization.C450Source13GroupedC13.valid5
#print axioms N11Formalization.C450Source13GroupedC13.valid6
#print axioms N11Formalization.C450Source13GroupedC13.valid7
#print axioms N11Formalization.C450Source13GroupedC13.valid8
#print axioms N11Formalization.C450Source13GroupedC13.valid9
#print axioms N11Formalization.C450Source13GroupedC13.valid10
#print axioms N11Formalization.C450Source13GroupedC13.valid11
#print axioms N11Formalization.C450Source13GroupedC13.valid12
#print axioms N11Formalization.C450Source13GroupedC13.valid13
#print axioms N11Formalization.C450Source13GroupedC13.valid14
#print axioms N11Formalization.C450Source13GroupedC13.bound
#print axioms N11Formalization.C450Source13GroupedC13.endpoint_checks
