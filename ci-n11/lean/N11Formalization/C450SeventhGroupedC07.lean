import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((98598351:ℚ)/156250000),((6584773211:ℚ)/10000000000),((-6264773211:ℚ)/9920000000),((-827385159:ℚ)/1609375000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5911471499:ℚ)/10000000000),((375708041034281028281844542256768825885336563901733667659:ℚ)/32363798425600000000000000000000000000000000000000000000000),((199596125365334546953143729:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((6547875861:ℚ)/10000000000),((6822370271:ℚ)/10000000000),((-6502370271:ℚ)/10300000000),((-18363627583:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((21298261:ℚ)/40000000),((78418242831366536743414755113881314168316688091755323031:ℚ)/6762102005468750000000000000000000000000000000000000000000),((199581164507955840657790809:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3392725731:ℚ)/5000000000),((1388233251:ℚ)/2000000000),((-1324233251:ℚ)/2136000000),((-28614531579:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1168057241:ℚ)/2500000000),((133788156756558822773494573948991706536000920019305808473:ℚ)/11994761035598400000000000000000000000000000000000000000000),((7977423484847991049305249:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((43151483:ℚ)/62500000),((109383807:ℚ)/156250000),((-104383807:ℚ)/169843750),((-121454449:ℚ)/228437500),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2156150449:ℚ)/5000000000),((11193552678864931135586780727948346005661640654056469:ℚ)/1022688797933731973171234130859375000000000000000000000),((48672776320230548040001:ℚ)/451250000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((6963629723:ℚ)/10000000000),((7059960657:ℚ)/10000000000),((-6739960657:ℚ)/10965000000),((-58832667507:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2060682909:ℚ)/5000000000),((646631092098621876013542364737393190677894578241770314009:ℚ)/59056468487148065185546875000000000000000000000000000000000),((199363222119233578598556601:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((3511510933:ℚ)/5000000000),((354482951:ℚ)/500000000),((-338482951:ℚ)/553000000),((-9894532799:ℚ)/18512500000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1960850649:ℚ)/5000000000),((9431637550142598180077409070470995554816489198723749853:ℚ)/869354278896321093750000000000000000000000000000000000000),((498319487841020787115849:ℚ)/4620800000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1763179457:ℚ)/2500000000),((7119357291:ℚ)/10000000000),((-6799357291:ℚ)/11107500000),((-14908615113:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((381816873:ℚ)/1000000000),((14456675443609942441579559146343611392312839778229991489779:ℚ)/1332226736661791464233398437500000000000000000000000000000000),((199327931859437156729015569:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((3541206859:ℚ)/5000000000),((714905547:ℚ)/1000000000),((-682905547:ℚ)/1115500000),((-29950861731:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((1855947539:ℚ)/5000000000),((37814306863702497514598917520021165687790330642085652627:ℚ)/3483923616260033609375000000000000000000000000000000000000),((1993282171706048732489041:ℚ)/18483200000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((222253423:ℚ)/312500000),((7178753559:ℚ)/10000000000),((-6858753559:ℚ)/11202500000),((-626760269:ℚ)/1171875000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3602637289:ℚ)/10000000000),((1676793110292540113469437349518910513742831530763591:ℚ)/154453382448005676269531250000000000000000000000000000),((199328651070949548520857769:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((1785451321:ℚ)/2500000000),((7208451559:ℚ)/10000000000),((-6888451559:ℚ)/11250000000),((-15109061889:ℚ)/28243750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((698022923:ℚ)/2000000000),((328885679858443719875695035358629727307352451005684827211437:ℚ)/30288029315185546875000000000000000000000000000000000000000000),((199329233557949524893493769:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7171500963:ℚ)/10000000000),((7238149471:ℚ)/10000000000),((-6918149471:ℚ)/11297500000),((-60703508667:ℚ)/113450000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3373999903:ℚ)/10000000000),((629896663478094186074761048532341139856036934242861257039:ℚ)/57997072468163036987304687500000000000000000000000000000000),((199329964630295749364024409:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7201196573:ℚ)/10000000000),((56780057:ℚ)/78125000),((-108560114:ℚ)/177265625),((-20323589719:ℚ)/37975000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((1626954053:ℚ)/5000000000),((13961725507661785012150754306704287282546226942000685027:ℚ)/1285254480232875299453735351562500000000000000000000000000),((194659027624894309989391:ℚ)/1805000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((1807723029:ℚ)/2500000000),((1824386259:ℚ)/2500000000),((-249198037:ℚ)/406875000),((-15309507261:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((97793151:ℚ)/312500000),((274293124778107455018572750434693472258757346735009:ℚ)/25245311338806152343750000000000000000000000000000000),((12458242033094101342559169:ℚ)/115520000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((7260587591:ℚ)/10000000000),((732724269:ℚ)/1000000000),((-700724269:ℚ)/1144000000),((-61505288319:ℚ)/114875000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((374983151:ℚ)/1250000000),((128823862955546905449512931428928282193551356405094724543:ℚ)/11854421703009600000000000000000000000000000000000000000000),((1993330493538192296829889:ℚ)/18483200000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7290283001:ℚ)/10000000000),((7356940261:ℚ)/10000000000),((-7036940261:ℚ)/11487500000),((-20590849003:ℚ)/38450000000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2864684119:ℚ)/10000000000),((7136509262423783719273102330382799491995276344187911019:ℚ)/656584399340342044830322265625000000000000000000000000000),((199334374759682703206446129:ℚ)/1848320000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3659989173:ℚ)/5000000000),((1854083789:ℚ)/2500000000),((-591361263:ℚ)/961250000),((-31019902557:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1361496653:ℚ)/5000000000),((41180876883684352989470781196697676557225663748628758047:ℚ)/3754209545156988525390625000000000000000000000000000000000),((12460805340078511974297729:ℚ)/115520000000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((7379368843:ℚ)/10000000000),((116808277:ℚ)/156250000),((-111808277:ℚ)/181718750),((-62574319587:ℚ)/117250000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2415449189:ℚ)/10000000000),((1086136066410831422501439686995038420442525042306077223:ℚ)/98993384132728672027587890625000000000000000000000000000),((194703687656593123603709:ℚ)/1805000000000000000000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((464922443:ℚ)/625000000),((3767561993:ℚ)/5000000000),((-515365999:ℚ)/837500000),((-1314767329:ℚ)/2462500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2063557899:ℚ)/10000000000),((195455577547213272928427695629030289426081761925959671:ℚ)/17810533549499511718750000000000000000000000000000000000),((49845215298564889726996201:ℚ)/462080000000000000000000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((7498149089:ℚ)/10000000000),((242896813:ℚ)/312500000),((-77632271:ℚ)/123125000),((-63643341801:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((819496071:ℚ)/5000000000),((12019820997802850186398699299040323419391644017555283:ℚ)/1041812729479980468750000000000000000000000000000000000),((26235889243103209:ℚ)/243200000000000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((3867853377:ℚ)/5000000000),((4123916523:ℚ)/5000000000),((-3963916523:ℚ)/6100000000),((-10963560131:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6318676343359379051888756801403712699813703095408373083:ℚ)/517091090625000000000000000000000000000000000000000000000),((13799951:ℚ)/128000000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((256587873:ℚ)/312500000),((634265303:ℚ)/625000000),((-204755101:ℚ)/270000000),((-2189290857:ℚ)/5000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2924407160633752924958796317926649958080751865783:ℚ)/184528125000000000000000000000000000000000000000000),((13799951:ℚ)/128000000)⟩
theorem valid20 : Valid seventh packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10111132717:ℚ)/10000000000),((2789745641:ℚ)/2000000000),((-2725745641:ℚ)/3200000000),((-29053398151:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((789971255954224557459590086844285912049989151896688907:ℚ)/40627200000000000000000000000000000000000000000000000000),((13799951:ℚ)/128000000)⟩
theorem valid21 : Valid seventh packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound seventh nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((1163:ℚ)/1600) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC07
#check @N11Formalization.C450SeventhGroupedC07.bound
#print axioms N11Formalization.C450SeventhGroupedC07.valid0
#print axioms N11Formalization.C450SeventhGroupedC07.valid1
#print axioms N11Formalization.C450SeventhGroupedC07.valid2
#print axioms N11Formalization.C450SeventhGroupedC07.valid3
#print axioms N11Formalization.C450SeventhGroupedC07.valid4
#print axioms N11Formalization.C450SeventhGroupedC07.valid5
#print axioms N11Formalization.C450SeventhGroupedC07.valid6
#print axioms N11Formalization.C450SeventhGroupedC07.valid7
#print axioms N11Formalization.C450SeventhGroupedC07.valid8
#print axioms N11Formalization.C450SeventhGroupedC07.valid9
#print axioms N11Formalization.C450SeventhGroupedC07.valid10
#print axioms N11Formalization.C450SeventhGroupedC07.valid11
#print axioms N11Formalization.C450SeventhGroupedC07.valid12
#print axioms N11Formalization.C450SeventhGroupedC07.valid13
#print axioms N11Formalization.C450SeventhGroupedC07.valid14
#print axioms N11Formalization.C450SeventhGroupedC07.valid15
#print axioms N11Formalization.C450SeventhGroupedC07.valid16
#print axioms N11Formalization.C450SeventhGroupedC07.valid17
#print axioms N11Formalization.C450SeventhGroupedC07.valid18
#print axioms N11Formalization.C450SeventhGroupedC07.valid19
#print axioms N11Formalization.C450SeventhGroupedC07.valid20
#print axioms N11Formalization.C450SeventhGroupedC07.valid21
#print axioms N11Formalization.C450SeventhGroupedC07.bound
#print axioms N11Formalization.C450SeventhGroupedC07.endpoint_checks
