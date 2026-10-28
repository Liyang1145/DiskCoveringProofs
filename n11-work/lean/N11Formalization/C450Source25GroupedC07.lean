import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3335331147:ℚ)/5000000000),((429634591:ℚ)/625000000),((-337634591:ℚ)/620000000),((-7445993441:ℚ)/16850000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4997159177:ℚ)/10000000000),((225949224316894163148905518671680572444939221901248572269:ℚ)/926918236718750000000000000000000000000000000000000000000),((15590113903304643788726083:ℚ)/55449600000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6790299039:ℚ)/10000000000),((1748432949:ℚ)/2500000000),((-1380432949:ℚ)/2527500000),((-45752691351:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4658047683:ℚ)/10000000000),((561079513150589867380126373900196314600418130807833758445357:ℚ)/2301556243750000000000000000000000000000000000000000000000000),((61610832684853057409435227:ℚ)/221798400000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1381980543:ℚ)/2000000000),((1410701899:ℚ)/2000000000),((-1116301899:ℚ)/2060000000),((-3121941629:ℚ)/6930000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((171777277:ℚ)/400000000),((12853694671483178712110880956356264381457720750517537737:ℚ)/53562020892187500000000000000000000000000000000000000000),((2434137330945907894855963:ℚ)/8871936000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((6969692727:ℚ)/10000000000),((3556639913:ℚ)/5000000000),((-402948559:ℚ)/742500000),((-47367234543:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4101404417:ℚ)/10000000000),((42859945140432274728051422615390775510487373241835095263047:ℚ)/178558975392187500000000000000000000000000000000000000000000),((167511955062033630402643:ℚ)/614400000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((878684393:ℚ)/1250000000),((7143162293:ℚ)/10000000000),((-5671162293:ℚ)/10490000000),((-1996053179:ℚ)/4390625000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((1949712227:ℚ)/5000000000),((1321868165962289895553713043280844202095144192382989361:ℚ)/5549253227472305297851562500000000000000000000000000000),((866924230732701395761:ℚ)/3200000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((705936357:ℚ)/1000000000),((448315187:ℚ)/625000000),((-118771729:ℚ)/219531250),((-4817427213:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3794631577:ℚ)/10000000000),((496227043083317267196035958572565166486437171958882067727:ℚ)/2082854458791406250000000000000000000000000000000000000000),((598957405961968820520163:ℚ)/2217984000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((283570007:ℚ)/400000000),((1800730487:ℚ)/2500000000),((-1432730487:ℚ)/2646250000),((-1937730063:ℚ)/4253000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3687016153:ℚ)/10000000000),((242535439208433078813591180277922402138103816940056540369:ℚ)/1017857599502556250000000000000000000000000000000000000000),((31841462502299368516121:ℚ)/118292480000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((3559567491:ℚ)/5000000000),((1446559837:ℚ)/2000000000),((-1152159837:ℚ)/2126500000),((-8118702473:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3576322779:ℚ)/10000000000),((8931595841714312884538890661126221034523810959126822310791:ℚ)/37477914462500000000000000000000000000000000000000000000000),((14877314252348824275944947:ℚ)/55449600000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((3574509009:ℚ)/5000000000),((3631337363:ℚ)/5000000000),((-2895337363:ℚ)/5340000000),((-24490581081:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((1731127803:ℚ)/5000000000),((3107707522183214118452293493016471420985510193990793673837:ℚ)/13038317389174218750000000000000000000000000000000000000000),((14828821240854651435293947:ℚ)/55449600000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((897362413:ℚ)/1250000000),((7292548593:ℚ)/10000000000),((-5820548593:ℚ)/10727500000),((-6156261717:ℚ)/13468750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3344468811:ℚ)/10000000000),((1334788564311787660382194910421968381102996055284695580107:ℚ)/5598738223731663131713867187500000000000000000000000000000),((307920968779380672625201:ℚ)/1155200000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3604389433:ℚ)/5000000000),((1838072849:ℚ)/2500000000),((-1470072849:ℚ)/2693750000),((-24759504897:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((25780431:ℚ)/80000000),((34687093138976179562068197730705860401807003674604933615171:ℚ)/144348065510374450683593750000000000000000000000000000000000),((13602465386369604234321:ℚ)/51200000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1453706581:ℚ)/2000000000),((7412027767:ℚ)/10000000000),((-5940027767:ℚ)/10870000000),((-3337119743:ℚ)/7310000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((592856561:ℚ)/2000000000),((257786709283114440402207345852380333174723183225382181607853:ℚ)/1072366928982160937500000000000000000000000000000000000000000),((780460359217806131885569:ℚ)/2957312000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((3664140157:ℚ)/5000000000),((3735878937:ℚ)/5000000000),((-2999878937:ℚ)/5482500000),((-25297261413:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1341038523:ℚ)/5000000000),((169067062484659353419814131487841598042185740748137374069:ℚ)/703053196275572204589843750000000000000000000000000000000),((4845102093832905991709521:ℚ)/18483200000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((3694010633:ℚ)/5000000000),((379559997:ℚ)/500000000),((-43708571:ℚ)/79000000),((-8522031899:ℚ)/18750000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1183692779:ℚ)/5000000000),((26443636927450296147742682158078417720811297929:ℚ)/108333764648437500000000000000000000000000000000),((4812164510284193291326681:ℚ)/18483200000000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((3753742231:ℚ)/5000000000),((3855309411:ℚ)/5000000000),((-3119309411:ℚ)/5625000000),((-26103680079:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1561913891:ℚ)/10000000000),((1851388988491753854320288547842371466529139850866358121443:ℚ)/7582255554199218750000000000000000000000000000000000000000),((4745801891484413061711769:ℚ)/18483200000000000000000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7626923761:ℚ)/10000000000),((8665258833:ℚ)/10000000000),((-7193258833:ℚ)/11440000000),((-17760771283:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((50700566090393314253187511214286986850577868078660181197:ℚ)/174912566400000000000000000000000000000000000000000000000),((32506599:ℚ)/128000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((2145426311:ℚ)/2500000000),((10571880467:ℚ)/10000000000),((-3033293489:ℚ)/4320000000),((-15468836799:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((165298851956164998261610478361246498352058951765638619:ℚ)/503884800000000000000000000000000000000000000000000000),((32506599:ℚ)/128000000)⟩
theorem valid16 : Valid source25 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((5244264171:ℚ)/5000000000),((14379637153:ℚ)/10000000000),((-12907637153:ℚ)/16000000000),((-13172792513:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1346995266129862500055820531745764775171548037527375999523:ℚ)/3385600000000000000000000000000000000000000000000000000000),((32506599:ℚ)/128000000)⟩
theorem valid17 : Valid source25 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source25 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source25 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source25 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC07
#check @N11Formalization.C450Source25GroupedC07.bound
#print axioms N11Formalization.C450Source25GroupedC07.valid0
#print axioms N11Formalization.C450Source25GroupedC07.valid1
#print axioms N11Formalization.C450Source25GroupedC07.valid2
#print axioms N11Formalization.C450Source25GroupedC07.valid3
#print axioms N11Formalization.C450Source25GroupedC07.valid4
#print axioms N11Formalization.C450Source25GroupedC07.valid5
#print axioms N11Formalization.C450Source25GroupedC07.valid6
#print axioms N11Formalization.C450Source25GroupedC07.valid7
#print axioms N11Formalization.C450Source25GroupedC07.valid8
#print axioms N11Formalization.C450Source25GroupedC07.valid9
#print axioms N11Formalization.C450Source25GroupedC07.valid10
#print axioms N11Formalization.C450Source25GroupedC07.valid11
#print axioms N11Formalization.C450Source25GroupedC07.valid12
#print axioms N11Formalization.C450Source25GroupedC07.valid13
#print axioms N11Formalization.C450Source25GroupedC07.valid14
#print axioms N11Formalization.C450Source25GroupedC07.valid15
#print axioms N11Formalization.C450Source25GroupedC07.valid16
#print axioms N11Formalization.C450Source25GroupedC07.valid17
#print axioms N11Formalization.C450Source25GroupedC07.bound
#print axioms N11Formalization.C450Source25GroupedC07.endpoint_checks
