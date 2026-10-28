import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((6301242811:ℚ)/10000000000),((6572931391:ℚ)/10000000000),((-6092931391:ℚ)/12400000000),((-39628699677:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5932808091:ℚ)/10000000000),((3353770953030062702798981216795976351319606502046038741701:ℚ)/211715856250000000000000000000000000000000000000000000000000),((1328151751934373106736263:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((1307776301:ℚ)/2000000000),((3405297027:ℚ)/5000000000),((-3165297027:ℚ)/6437500000),((-2752811369:ℚ)/7120000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1336957987:ℚ)/2500000000),((917602550151184268327933427021032492186201259876290369:ℚ)/58089445600000000000000000000000000000000000000000000000),((992532569549152385130301:ℚ)/10830000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6776510321:ℚ)/10000000000),((1732355279:ℚ)/2500000000),((-1612355279:ℚ)/3337500000),((-42955572247:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2349140847:ℚ)/5000000000),((10976744806169402798530233040255297761013123169333827797209:ℚ)/714428311043750000000000000000000000000000000000000000000000),((82345899892527945254343:ℚ)/902500000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6895321349:ℚ)/10000000000),((1397766729:ℚ)/2000000000),((-1301766729:ℚ)/2717500000),((-43787249443:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2170141189:ℚ)/5000000000),((11315640988688668346420673535123730287215509707732898655521:ℚ)/746370083525976562500000000000000000000000000000000000000000),((157754473281872726683429:ℚ)/1732800000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((695472607:ℚ)/1000000000),((7048245529:ℚ)/10000000000),((-6568245529:ℚ)/13706250000),((-631472607:ℚ)/1580000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((830103097:ℚ)/2000000000),((4268288512310451114054961039712575210805651054417819:ℚ)/281571491406250000000000000000000000000000000000000000),((69129144833767170271597:ℚ)/760000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7014130279:ℚ)/10000000000),((7107656783:ℚ)/10000000000),((-6627656783:ℚ)/13825000000),((-44618911953:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3952200143:ℚ)/10000000000),((4544633089483925254646758310068319287371683333359609361663:ℚ)/299842983018701171875000000000000000000000000000000000000000),((1312291770570787168635047:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((7073533991:ℚ)/10000000000),((356868109:ℚ)/500000000),((-332868109:ℚ)/697187500),((-45034737937:ℚ)/112025000000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((935993583:ℚ)/2500000000),((11809178130058374941969780529702738243817326178510667600689:ℚ)/784123440336214843750000000000000000000000000000000000000000),((3277104039119049179263:ℚ)/36100000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((443952229:ℚ)/625000000),((286682697:ℚ)/400000000),((-267482697:ℚ)/560125000),((-314185067:ℚ)/781250000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3635614847:ℚ)/10000000000),((2356831187526199856546884650005774867505715356024263:ℚ)/156497117131948471069335937500000000000000000000000000),((331013981500558256359:ℚ)/3648000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((7132937217:ℚ)/10000000000),((7196772521:ℚ)/10000000000),((-6716772521:ℚ)/14062500000),((-45450560519:ℚ)/112975000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3524077731:ℚ)/10000000000),((407152497530070423153443382473770793604203606278612110211:ℚ)/27036366316113281250000000000000000000000000000000000000000),((1309686957064246406289143:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((1790659663:ℚ)/2500000000),((722647747:ℚ)/1000000000),((-674647747:ℚ)/1412187500),((-11414617641:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((681810117:ℚ)/2000000000),((24260015792747260686710837197963603292356208205295181777:ℚ)/1611001311693450927734375000000000000000000000000000000000),((13091114564642008054207:ℚ)/144400000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((719233997:ℚ)/1000000000),((14172231:ℚ)/19531250),((-423511392:ℚ)/886328125),((-655233997:ℚ)/1627500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((411270857:ℚ)/1250000000),((306858110433689937090332601537052049083247210716464877:ℚ)/20377750954394531250000000000000000000000000000000000000),((3833605004664587668579:ℚ)/42304687500000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((7222041173:ℚ)/10000000000),((7285886931:ℚ)/10000000000),((-2268628977:ℚ)/4746875000),((-46074288211:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1583495857:ℚ)/5000000000),((214034196840796978432421287683020717140454038871212980215083:ℚ)/14213985385600000000000000000000000000000000000000000000000000),((3923892337234986642836509:ℚ)/43320000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-1:ℚ)/2),((-7:ℚ)/16),((3625871131:ℚ)/5000000000),((914448931:ℚ)/1250000000),((-854448931:ℚ)/1787500000),((-23141097917:ℚ)/57437500000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((1519501413:ℚ)/5000000000),((7650272924687516579521416386885460586758879254167737770711:ℚ)/508070402238464355468750000000000000000000000000000000000000),((20428004201341225907503:ℚ)/225625000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7281443239:ℚ)/10000000000),((293811833:ℚ)/400000000),((-274611833:ℚ)/574375000),((-15496700891:ℚ)/38450000000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2905563537:ℚ)/10000000000),((576108663510782232851927877111917027068101300472110601:ℚ)/38261839935699462890625000000000000000000000000000000000),((2090914630867521743447:ℚ)/23104000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((913893013:ℚ)/1250000000),((1480940833:ℚ)/2000000000),((-1384940833:ℚ)/2883750000),((-5837251091:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2765884489:ℚ)/10000000000),((223654195217419254484312956179415303574073854669964958437:ℚ)/14766430999060058593750000000000000000000000000000000000000),((52262200583814294805447:ℚ)/577600000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((1842636377:ℚ)/2500000000),((7464111963:ℚ)/10000000000),((-6984111963:ℚ)/14537500000),((-1682636377:ℚ)/4187500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((615878799:ℚ)/2500000000),((24248564360846832533955139261162542164419371710172111031:ℚ)/1601199504089355468750000000000000000000000000000000000000),((3916266873131046806960461:ℚ)/43320000000000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7429946483:ℚ)/10000000000),((1504703847:ℚ)/2000000000),((-1408703847:ℚ)/2931250000),((-47529625381:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((529851487:ℚ)/2500000000),((6108065753199516851729687014261553091178724400532080904301:ℚ)/403388992912500000000000000000000000000000000000000000000000),((156515333121142568177221:ℚ)/1732800000000000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((46808419:ℚ)/62500000),((7761143289:ℚ)/10000000000),((-2427047763:ℚ)/4925000000),((-299658933:ℚ)/762500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((106782007:ℚ)/625000000),((8541194748273463889880828978797856880932113432422503:ℚ)/545840539550781250000000000000000000000000000000000000),((112824641083:ℚ)/1250000000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((7726945287:ℚ)/10000000000),((8236369559:ℚ)/10000000000),((-7756369559:ℚ)/15250000000),((-49608617009:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4492368894741531541134454990382937964719023531710759373161:ℚ)/276632755200000000000000000000000000000000000000000000000000),((18007:ℚ)/200000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8202124487:ℚ)/10000000000),((1013705957:ℚ)/1000000000),((-965705957:ℚ)/1620000000),((-52934871409:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13272570933525186450214658266310186478666142640765359393061:ℚ)/691200000000000000000000000000000000000000000000000000000000),((18007:ℚ)/200000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((78927117:ℚ)/78125000),((13937869403:ℚ)/10000000000),((-13457869403:ℚ)/20000000000),((-517489819:ℚ)/1725000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((532333739956778976692202627766449887228084539919279:ℚ)/24060717773437500000000000000000000000000000000000000),((18007:ℚ)/200000)⟩
theorem valid20 : Valid eighth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound eighth nn0 nn1 Qcell ((919:ℚ)/1280) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC09
#check @N11Formalization.C450EighthGroupedC09.bound
#print axioms N11Formalization.C450EighthGroupedC09.valid0
#print axioms N11Formalization.C450EighthGroupedC09.valid1
#print axioms N11Formalization.C450EighthGroupedC09.valid2
#print axioms N11Formalization.C450EighthGroupedC09.valid3
#print axioms N11Formalization.C450EighthGroupedC09.valid4
#print axioms N11Formalization.C450EighthGroupedC09.valid5
#print axioms N11Formalization.C450EighthGroupedC09.valid6
#print axioms N11Formalization.C450EighthGroupedC09.valid7
#print axioms N11Formalization.C450EighthGroupedC09.valid8
#print axioms N11Formalization.C450EighthGroupedC09.valid9
#print axioms N11Formalization.C450EighthGroupedC09.valid10
#print axioms N11Formalization.C450EighthGroupedC09.valid11
#print axioms N11Formalization.C450EighthGroupedC09.valid12
#print axioms N11Formalization.C450EighthGroupedC09.valid13
#print axioms N11Formalization.C450EighthGroupedC09.valid14
#print axioms N11Formalization.C450EighthGroupedC09.valid15
#print axioms N11Formalization.C450EighthGroupedC09.valid16
#print axioms N11Formalization.C450EighthGroupedC09.valid17
#print axioms N11Formalization.C450EighthGroupedC09.valid18
#print axioms N11Formalization.C450EighthGroupedC09.valid19
#print axioms N11Formalization.C450EighthGroupedC09.valid20
#print axioms N11Formalization.C450EighthGroupedC09.bound
#print axioms N11Formalization.C450EighthGroupedC09.endpoint_checks
