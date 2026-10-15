import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7022556103:ℚ)/10000000000),((3593597263:ℚ)/5000000000),((-9244791789:ℚ)/9920000000),((-41157892721:ℚ)/50075000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((3923304479:ℚ)/10000000000),((39815978648513484125961656373025479494519539:ℚ)/122390282361856000000000000000000000000000000),((13887956871923039777226513:ℚ)/14786560000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((885262129:ℚ)/1250000000),((7246660629:ℚ)/10000000000),((-18667981887:ℚ)/20030000000),((-1732278301:ℚ)/2106250000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((3713043693:ℚ)/10000000000),((72417584408544608713531900756622327370557137682754444327:ℚ)/222814116160244873046875000000000000000000000000000000000),((154366534691869368369537:ℚ)/163840000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((714163483:ℚ)/1000000000),((90954913:ℚ)/125000000),((-78154913:ℚ)/84250000),((-247008493:ℚ)/298750000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((3490770409:ℚ)/10000000000),((4254505937974325531476473766821646912736523198724697:ℚ)/13343371118853759765625000000000000000000000000000000),((8720885190927490979313:ℚ)/9241600000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3585701291:ℚ)/5000000000),((913265629:ℚ)/1250000000),((-2355796887:ℚ)/2539375000),((-21099909037:ℚ)/25512500000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((843597731:ℚ)/2500000000),((804081773422828692527138995948661485669305401529490811087:ℚ)/2522666506928257751464843750000000000000000000000000000000),((873454349892837006532857:ℚ)/924160000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((8183:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1440233917:ℚ)/2000000000),((7320990873:ℚ)/10000000000),((-18890972619:ℚ)/20410000000),((-8481637419:ℚ)/10228750000),((9888211123:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((37416203:ℚ)/250000000),((1627009593:ℚ)/5000000000),((70548505541013132591205195370055703307314139502584293223527:ℚ)/223436794826859250000000000000000000000000000000000000000000),((55944810098983692242630433:ℚ)/59146240000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8183:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((8183:ℚ)/12800),((4101:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((902006601:ℚ)/1250000000),((7335856611:ℚ)/10000000000),((-18935569833:ℚ)/20457500000),((-5314046207:ℚ)/6407812500),((4940065779:ℚ)/5000000000),((1236026391:ℚ)/1250000000),((774947369:ℚ)/5000000000),((399024437:ℚ)/1250000000),((211394708416498483746668462920606350944171919432642595089413:ℚ)/669603888089216532897949218750000000000000000000000000000000),((55988558552159105440868217:ℚ)/59146240000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((8183:ℚ)/12800) ((4101:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7230935847:ℚ)/10000000000),((7350722247:ℚ)/10000000000),((-6326722247:ℚ)/6835000000),((-42616550929:ℚ)/51381250000),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((1564596959:ℚ)/5000000000),((42575960110926934562992752070395917473047612721648119935354703:ℚ)/134879165551324049218750000000000000000000000000000000000000000),((56032323755258025424580193:ℚ)/59146240000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((452863669:ℚ)/625000000),((3682793891:ℚ)/5000000000),((-9512381673:ℚ)/10276250000),((-2670045683:ℚ)/3218750000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3064941737:ℚ)/10000000000),((22710247933975542010769036897753004517387366623274024590777:ℚ)/71954581300382678222656250000000000000000000000000000000000),((14019026427718814950649337:ℚ)/14786560000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7260701381:ℚ)/10000000000),((7380453217:ℚ)/10000000000),((-19069359651:ℚ)/20600000000),((-14274969889:ℚ)/17206250000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((5998717:ℚ)/20000000),((510460113607839942767045980941726963848507654939137303177491:ℚ)/1617536673348242187500000000000000000000000000000000000000000),((56119904421610206302506353:ℚ)/59146240000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7275583877:ℚ)/10000000000),((7395318551:ℚ)/10000000000),((-6371318551:ℚ)/6882500000),((-42929087139:ℚ)/51737500000),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((293235483:ℚ)/1000000000),((2753606446394093843093519362745316536851900460444330837733151:ℚ)/8726689805189634204101562500000000000000000000000000000000000),((56163719884170720492387777:ℚ)/59146240000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((1458093239:ℚ)/2000000000),((297001957:ℚ)/400000000),((-768125871:ℚ)/827800000),((-8606652673:ℚ)/10395000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((143191547:ℚ)/500000000),((3097225171980639379130693321001820387966911779413638113:ℚ)/9729369652853466000000000000000000000000000000000000000),((90002241743890602468873:ℚ)/94633984000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7320230299:ℚ)/10000000000),((7454778907:ℚ)/10000000000),((-306227567:ℚ)/330000000),((-43241612093:ℚ)/52212500000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((21263753:ℚ)/78125000),((3435572168337429774374114513148373697853685932014885509:ℚ)/10795534818750000000000000000000000000000000000000000000),((56339149334297765596414473:ℚ)/59146240000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1469998741:ℚ)/2000000000),((935563563:ℚ)/1250000000),((-2422690689:ℚ)/2610625000),((-8689991187:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((25720621:ℚ)/100000000),((38930332093930559898779149412605635586561413460999215724169:ℚ)/122367044725168507385253906250000000000000000000000000000000),((881671322425879317739113:ℚ)/924160000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((368987821:ℚ)/500000000),((7543966561:ℚ)/10000000000),((-19559899683:ℚ)/20980000000),((-2182914747:ℚ)/2646250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2413316311:ℚ)/10000000000),((83707443427823803758022429608506909427267461858416937456799187:ℚ)/258665307754808050000000000000000000000000000000000000000000000),((56602796449624916314396017:ℚ)/59146240000000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((7439279817:ℚ)/10000000000),((3801711569:ℚ)/5000000000),((-9869134707:ℚ)/10585000000),((-44074958719:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2060211209:ℚ)/10000000000),((42716627198656941954429813371930454980773422342010553402107:ℚ)/132103746897491601562500000000000000000000000000000000000000),((491419239:ℚ)/512000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((1499760113:ℚ)/2000000000),((1960308851:ℚ)/2500000000),((-1704308851:ℚ)/1780000000),((-8898320791:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((816865103:ℚ)/5000000000),((1642656643156048382134484247682074719019139808280596630111:ℚ)/4619697105450000000000000000000000000000000000000000000000),((491419239:ℚ)/512000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((7736858431:ℚ)/10000000000),((1009878361:ℚ)/1250000000),((-377947869:ℚ)/395000000),((-46158009017:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((2781359994865603029293133109547053378960613945021108629:ℚ)/7876683211718750000000000000000000000000000000000000000),((491419239:ℚ)/512000000)⟩
theorem valid16 : Valid source26 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((3987439557:ℚ)/5000000000),((9030021627:ℚ)/10000000000),(-1:ℚ),((-23912076899:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2215793342441023141983229461332989889:ℚ)/5248800000000000000000000000000000000),((491419239:ℚ)/512000000)⟩
theorem valid17 : Valid source26 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((1115831959:ℚ)/1250000000),((10931443481:ℚ)/10000000000),(-1:ℚ),((-6810823713:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((165509466407297885610621221007571927:ℚ)/375000000000000000000000000000000000),((491419239:ℚ)/512000000)⟩
theorem valid18 : Valid source26 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((10829194159:ℚ)/10000000000),((294662237:ℚ)/200000000),(-1:ℚ),((-67804359113:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2928515088841203691090314479:ℚ)/6094080000000000000000000000),((491419239:ℚ)/512000000)⟩
theorem valid19 : Valid source26 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((4063:ℚ)/6400) ((8183:ℚ)/12800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((8183:ℚ)/12800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((8183:ℚ)/12800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source26 nn0 nn1 Qcell ((8183:ℚ)/12800) ((8221:ℚ)/12800) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source26 nn0 nn1 Qcell ((8221:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source26 nn0 nn1 Qcell ((8183:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((4139:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((4177:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source26 nn0 nn1 Qcell ((4177:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC02
#check @N11Formalization.C450Source26GroupedC02.bound
#print axioms N11Formalization.C450Source26GroupedC02.valid0
#print axioms N11Formalization.C450Source26GroupedC02.valid1
#print axioms N11Formalization.C450Source26GroupedC02.valid2
#print axioms N11Formalization.C450Source26GroupedC02.valid3
#print axioms N11Formalization.C450Source26GroupedC02.valid4
#print axioms N11Formalization.C450Source26GroupedC02.valid5
#print axioms N11Formalization.C450Source26GroupedC02.valid6
#print axioms N11Formalization.C450Source26GroupedC02.valid7
#print axioms N11Formalization.C450Source26GroupedC02.valid8
#print axioms N11Formalization.C450Source26GroupedC02.valid9
#print axioms N11Formalization.C450Source26GroupedC02.valid10
#print axioms N11Formalization.C450Source26GroupedC02.valid11
#print axioms N11Formalization.C450Source26GroupedC02.valid12
#print axioms N11Formalization.C450Source26GroupedC02.valid13
#print axioms N11Formalization.C450Source26GroupedC02.valid14
#print axioms N11Formalization.C450Source26GroupedC02.valid15
#print axioms N11Formalization.C450Source26GroupedC02.valid16
#print axioms N11Formalization.C450Source26GroupedC02.valid17
#print axioms N11Formalization.C450Source26GroupedC02.valid18
#print axioms N11Formalization.C450Source26GroupedC02.valid19
#print axioms N11Formalization.C450Source26GroupedC02.bound
#print axioms N11Formalization.C450Source26GroupedC02.endpoint_checks
