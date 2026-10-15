import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6281792229:ℚ)/10000000000),((6550661419:ℚ)/10000000000),((-17411984257:ℚ)/49600000000),((-5257792229:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1195686067:ℚ)/2000000000),((113694032723254293916418420414092195642585512442487415169:ℚ)/5081180550000000000000000000000000000000000000000000000000),((118205830565297592209983671:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((651950299:ℚ)/1000000000),((848550623:ℚ)/1250000000),((-2265651869:ℚ)/6437500000),((-183183433:ℚ)/712000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((168676647:ℚ)/312500000),((1293010914627894857400428848884650742513489316763527:ℚ)/58089445600000000000000000000000000000000000000000000),((1825590284672323158919919:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1351439747:ℚ)/2000000000),((1726817593:ℚ)/2500000000),((-4620452779:ℚ)/13350000000),((-1146639747:ℚ)/4348000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4754100907:ℚ)/10000000000),((994709203749923636942391785231680786142588550511926979:ℚ)/45723411906800000000000000000000000000000000000000000000),((7203890227812178373240639:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6876041469:ℚ)/10000000000),((1741675391:ℚ)/2500000000),((-4665026173:ℚ)/13587500000),((-5852041469:ℚ)/21930000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((275013741:ℚ)/625000000),((128491822861230135021924980404737246317754615276604106137:ℚ)/5970960668207812500000000000000000000000000000000000000000),((7154746107130309902526191:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((693546163:ℚ)/1000000000),((7026131789:ℚ)/10000000000),((-18838395367:ℚ)/54825000000),((-591146163:ℚ)/2212000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((842586989:ℚ)/2000000000),((16615406103517374734630354084809388022297013039345281:ℚ)/772632172418750000000000000000000000000000000000000000),((114139197529174828159820231:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6994881013:ℚ)/10000000000),((442847567:ℚ)/625000000),((-1188542701:ℚ)/3456250000),((-5970881013:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1004368743:ℚ)/2500000000),((51551173514539290571927438010837763491458800980860949333:ℚ)/2398743864149609375000000000000000000000000000000000000000),((444544576542749687909879:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((176357491:ℚ)/250000000),((3572494719:ℚ)/5000000000),((-9597484157:ℚ)/27887500000),((-50252497:ℚ)/187500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3812578977:ℚ)/10000000000),((23133708558217858205035812445107595553687635580413:ℚ)/1077121496200561523437500000000000000000000000000000),((28367144937043318677033071:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((711371753:ℚ)/1000000000),((7174703283:ℚ)/10000000000),((-19284109849:ℚ)/56250000000),((-608971753:ℚ)/2259500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3596630641:ℚ)/10000000000),((4621892716793551452559388683225963957590214779956923:ℚ)/216290930528906250000000000000000000000000000000000000),((113077231239218566553729479:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1785856551:ℚ)/2500000000),((1801104227:ℚ)/2500000000),((-4843312681:ℚ)/14121875000),((-1529856551:ℚ)/5672500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((348387247:ℚ)/1000000000),((275328150809121517218794244142541594714565727735266297:ℚ)/12888010493547607421875000000000000000000000000000000000),((7056900805025321172593319:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((71731347:ℚ)/100000000),((1446826063:ℚ)/2000000000),((-3892478189:ℚ)/11345000000),((-61491347:ℚ)/227850000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((1683750071:ℚ)/5000000000),((1194236514345132356795552198986781380646586298327237:ℚ)/55916548618858593750000000000000000000000000000000000),((4509753318422249092710159:ℚ)/73932800000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((7202843021:ℚ)/10000000000),((3631921753:ℚ)/5000000000),((-9775765259:ℚ)/28481250000),((-475295617:ℚ)/1760000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((811781139:ℚ)/2500000000),((1105129256562304805494198300343940428079576391301334279:ℚ)/51757798400000000000000000000000000000000000000000000000),((28144372863925868820233599:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-3:ℚ)/8),((-5:ℚ)/16),((7232551169:ℚ)/10000000000),((1823389121:ℚ)/2500000000),((-4910167363:ℚ)/14300000000),((-6208551169:ℚ)/22975000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((390285271:ℚ)/1250000000),((694113452945662963021744850953336338244199535649236832813:ℚ)/32516505743261718750000000000000000000000000000000000000000),((7025711771965890672893551:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7262259147:ℚ)/10000000000),((7323269253:ℚ)/10000000000),((-19729807759:ℚ)/57437500000),((-6238259147:ℚ)/23070000000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((374051673:ℚ)/1250000000),((176375191147613478813137163277121775088670921375529103:ℚ)/8264557426111083984375000000000000000000000000000000000),((112245523627932388729168599:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1458393391:ℚ)/2000000000),((7382694169:ℚ)/10000000000),((-19908082507:ℚ)/57675000000),((-1253593391:ℚ)/4652000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2856832207:ℚ)/10000000000),((10368094106875258062148707345537621965098650431269411847:ℚ)/483866410977200000000000000000000000000000000000000000000),((5902041602804755822529509:ℚ)/97280000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((7351382073:ℚ)/10000000000),((1860529569:ℚ)/2500000000),((-5021588707:ℚ)/14537500000),((-6327382073:ℚ)/23450000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1282435439:ℚ)/5000000000),((6022162533754659588138018110477632731199369489332464769089:ℚ)/281196252110156250000000000000000000000000000000000000000000),((6988045437364530921437871:ℚ)/115520000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7410796541:ℚ)/10000000000),((7501541593:ℚ)/10000000000),((-2894946397:ℚ)/8375000000),((-6386796541:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((447206247:ℚ)/2000000000),((9868167754111316089201045672309198438150690460280484373:ℚ)/461015991900000000000000000000000000000000000000000000000),((111479616832414852092544639:ℚ)/1848320000000000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((3735105187:ℚ)/5000000000),((3869613663:ℚ)/5000000000),((-10488840989:ℚ)/29550000000),((-3223105187:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1850751863:ℚ)/10000000000),((146973403096772118199938055537302910298249740206305025701:ℚ)/6707288550000000000000000000000000000000000000000000000000),((731783331038981:ℚ)/12160000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((7707859651:ℚ)/10000000000),((8214566081:ℚ)/10000000000),((-22403698243:ℚ)/61000000000),((-2227953217:ℚ)/8640000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1842692132974952237919558451633107039520113011772864527:ℚ)/81965260800000000000000000000000000000000000000000000000),((61081:ℚ)/1024000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((4091565961:ℚ)/5000000000),((5057799517:ℚ)/5000000000),((-14053398551:ℚ)/32400000000),((-3579565961:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((17571571497837128193116208688053287901190555005912050299:ℚ)/691200000000000000000000000000000000000000000000000000000),((61081:ℚ)/1024000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((1260495273:ℚ)/1250000000),((3479202807:ℚ)/2500000000),((-9877608421:ℚ)/20000000000),((-1132495273:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((22748747528570832378417958486683734309092921268810987:ℚ)/788421600000000000000000000000000000000000000000000000),((61081:ℚ)/1024000)⟩
theorem valid19 : Valid ninth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4557:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((4557:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((4557:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((919:ℚ)/1280) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound ninth nn0 nn1 Qcell ((919:ℚ)/1280) ((469:ℚ)/640) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((469:ℚ)/640) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC11
#check @N11Formalization.C450NinthGroupedC11.bound
#print axioms N11Formalization.C450NinthGroupedC11.valid0
#print axioms N11Formalization.C450NinthGroupedC11.valid1
#print axioms N11Formalization.C450NinthGroupedC11.valid2
#print axioms N11Formalization.C450NinthGroupedC11.valid3
#print axioms N11Formalization.C450NinthGroupedC11.valid4
#print axioms N11Formalization.C450NinthGroupedC11.valid5
#print axioms N11Formalization.C450NinthGroupedC11.valid6
#print axioms N11Formalization.C450NinthGroupedC11.valid7
#print axioms N11Formalization.C450NinthGroupedC11.valid8
#print axioms N11Formalization.C450NinthGroupedC11.valid9
#print axioms N11Formalization.C450NinthGroupedC11.valid10
#print axioms N11Formalization.C450NinthGroupedC11.valid11
#print axioms N11Formalization.C450NinthGroupedC11.valid12
#print axioms N11Formalization.C450NinthGroupedC11.valid13
#print axioms N11Formalization.C450NinthGroupedC11.valid14
#print axioms N11Formalization.C450NinthGroupedC11.valid15
#print axioms N11Formalization.C450NinthGroupedC11.valid16
#print axioms N11Formalization.C450NinthGroupedC11.valid17
#print axioms N11Formalization.C450NinthGroupedC11.valid18
#print axioms N11Formalization.C450NinthGroupedC11.valid19
#print axioms N11Formalization.C450NinthGroupedC11.bound
#print axioms N11Formalization.C450NinthGroupedC11.endpoint_checks
