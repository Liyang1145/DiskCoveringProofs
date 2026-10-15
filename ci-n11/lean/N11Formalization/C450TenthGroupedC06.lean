import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((99921339:ℚ)/156250000),((166992239:ℚ)/250000000),((-1708914629:ℚ)/2480000000),((-90921339:ℚ)/160937500),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1141696777:ℚ)/2000000000),((79628471054255710083147373973916694453820803063075695413:ℚ)/3034106102400000000000000000000000000000000000000000000000),((42010769450529958444299:ℚ)/231040000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((663265157:ℚ)/1000000000),((3399267911:ℚ)/5000000000),((-34831947021:ℚ)/51500000000),((-605665157:ℚ)/1049000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5100557063:ℚ)/10000000000),((5886602385493363091395346618642191377428634502266612433855159:ℚ)/234851149126367187500000000000000000000000000000000000000000000),((16802169010538617740589499:ℚ)/92416000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((6751489451:ℚ)/10000000000),((216168083:ℚ)/312500000),((-2217848913:ℚ)/3278125000),((-6175489451:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4770487691:ℚ)/10000000000),((786917990894853959442286960525190499907824012855263046589:ℚ)/31391282938599014282226562500000000000000000000000000000000),((262565827135725480148439:ℚ)/1444000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((6870324203:ℚ)/10000000000),((6976798843:ℚ)/10000000000),((-23874929091:ℚ)/35600000000),((-6294324203:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2208923757:ℚ)/5000000000),((5018386982616080096719770370189434924650580756588153484881:ℚ)/204618353764062500000000000000000000000000000000000000000000),((67212945943408601776369331:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((866217557:ℚ)/1250000000),((10994091:ℚ)/15625000),((-112935001:ℚ)/168359375),((-794217557:ℚ)/1358750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((169252219:ℚ)/400000000),((3458214121900756690465035574984679894737021499744729751:ℚ)/140964907724975049495697021484375000000000000000000000000),((1312837868918429922837:ℚ)/7220000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1747288997:ℚ)/2500000000),((7095636867:ℚ)/10000000000),((-72932005537:ℚ)/108700000000),((-1603288997:ℚ)/2741250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4036695959:ℚ)/10000000000),((26314634327222007173839974143066072729495760546701457965669523:ℚ)/1072366928982160937500000000000000000000000000000000000000000000),((67221757822758211257273091:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7048570817:ℚ)/10000000000),((3562672949:ℚ)/5000000000),((-12209800813:ℚ)/18275000000),((-6472570817:ℚ)/11012500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((479098311:ℚ)/1250000000),((179723306271809903418457557619782567496448839904446884199463:ℚ)/7401913400792260742187500000000000000000000000000000000000000),((16804987717333882724790419:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7078277973:ℚ)/10000000000),((894381843:ℚ)/1250000000),((-9198200273:ℚ)/13765625000),((-6502277973:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1863434391:ℚ)/5000000000),((181613327513508985598463016971808762968340626572923479803947:ℚ)/7478411220015370845794677734375000000000000000000000000000000),((1050347603147996996003831:ℚ)/5776000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7107984961:ℚ)/10000000000),((3592381703:ℚ)/5000000000),((-36956198733:ℚ)/55300000000),((-6531984961:ℚ)/11107500000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((904500249:ℚ)/2500000000),((18099396118925567240077011906601124810431454285109494531403169:ℚ)/745160810482560937500000000000000000000000000000000000000000000),((16806142207238668742558971:ℚ)/92416000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7137691781:ℚ)/10000000000),((7214471889:ℚ)/10000000000),((-74239190779:ℚ)/111075000000),((-285290947:ℚ)/485000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3505907819:ℚ)/10000000000),((122360156590363739208878168055230646380201855718084447111409:ℚ)/5036774051651385498046875000000000000000000000000000000000000),((67226917552375075498153099:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7167398437:ℚ)/10000000000),((7244180193:ℚ)/10000000000),((-74565982123:ℚ)/111550000000),((-6591398437:ℚ)/11202500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3390268813:ℚ)/10000000000),((169300196135832616480743677923050419546461108214108097818330033:ℚ)/6967847232520067218750000000000000000000000000000000000000000000),((67229292770704956315562731:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((719710493:ℚ)/1000000000),((3636944161:ℚ)/5000000000),((-37446385771:ℚ)/56012500000),((-662110493:ℚ)/1125000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((408838421:ℚ)/1250000000),((8445160639997559903953748763252992673179985382137262921:ℚ)/347520110508012771606445312500000000000000000000000000000),((16807923621050467966699499:ℚ)/92416000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7226811263:ℚ)/10000000000),((7303596277:ℚ)/10000000000),((-8357728783:ℚ)/12500000000),((-6650811263:ℚ)/11297500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1573387929:ℚ)/5000000000),((6058843398164249008264477048568351978434088523554214294839733:ℚ)/249284191894531250000000000000000000000000000000000000000000000),((67234122692205079527888851:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7256517437:ℚ)/10000000000),((366665203:ℚ)/500000000),((-3777317233:ℚ)/5648750000),((-6680517437:ℚ)/11345000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((301793539:ℚ)/1000000000),((352456888390756510508313409035958102746759886283574523563:ℚ)/14499268117040759246826171875000000000000000000000000000000),((168091443486380270577971:ℚ)/924160000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((1457244691:ℚ)/2000000000),((3681505837:ℚ)/5000000000),((-37936564207:ℚ)/56725000000),((-1342044691:ℚ)/2278500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((360440927:ℚ)/1250000000),((575949488071804818628140621899769495713305052164364970940342253:ℚ)/23689810579652357519531250000000000000000000000000000000000000000),((16809764647758594269875811:ℚ)/92416000000000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((3657964659:ℚ)/5000000000),((7392719121:ℚ)/10000000000),((-76199910331:ℚ)/113925000000),((-3369964659:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((2742732927:ℚ)/10000000000),((21175474543347058373812223265698022467421799983876979543777:ℚ)/870862259943457031250000000000000000000000000000000000000000),((67241566281506375130855179:ℚ)/369664000000000000000000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7345635029:ℚ)/10000000000),((7452133521:ℚ)/10000000000),((-5911805287:ℚ)/8800000000),((-6769635029:ℚ)/11535000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2594511751:ℚ)/10000000000),((2417213546606451228737891188177645958444215928749398237:ℚ)/98387686375000000000000000000000000000000000000000000000),((67250737065884046666906379:ℚ)/369664000000000000000000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((7405045999:ℚ)/10000000000),((7511547277:ℚ)/10000000000),((-25835673349:ℚ)/38450000000),((-6829045999:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1134950841:ℚ)/5000000000),((11807702414838318747961618150690671516039917664643683595094799:ℚ)/480538821780094531250000000000000000000000000000000000000000000),((67255937859467820017114851:ℚ)/369664000000000000000000000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((3732228191:ℚ)/5000000000),((7630372919:ℚ)/10000000000),((-78814102109:ℚ)/116300000000),((-3444228191:ℚ)/5910000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((236431497:ℚ)/1250000000),((2390418855949555793118579224020616339717228723756599489352991:ℚ)/95387534255192187500000000000000000000000000000000000000000000),((88510343912565529:ℚ)/486400000000000000)⟩
theorem valid18 : Valid tenth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((7583275439:ℚ)/10000000000),((7868017127:ℚ)/10000000000),((-81428188397:ℚ)/118200000000),((-7007275439:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((663537147:ℚ)/10000000000),((49098127906238015377898146174948569912007047531169503995969:ℚ)/1888789399650000000000000000000000000000000000000000000000000),((176977784521210441:ℚ)/972800000000000000)⟩
theorem valid19 : Valid tenth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((977613387:ℚ)/1250000000),((8343280153:ℚ)/10000000000),((-1420591503:ℚ)/2000000000),((-301871129:ℚ)/540000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1010252248375457761661127365165551982495323116102704573:ℚ)/36450000000000000000000000000000000000000000000000000000),((5821439:ℚ)/32000000)⟩
theorem valid20 : Valid tenth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8296147229:ℚ)/10000000000),((10244082231:ℚ)/10000000000),((-107564904541:ℚ)/129600000000),((-7720147229:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1511270367513218456661551004804431367005269579308610696093:ℚ)/40814668800000000000000000000000000000000000000000000000000),((5821439:ℚ)/32000000)⟩
theorem valid21 : Valid tenth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((10196879511:ℚ)/10000000000),((14045023557:ℚ)/10000000000),((-149375259127:ℚ)/160000000000),((-3206959837:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((25209158003752087991014748730338045487911:ℚ)/541696000000000000000000000000000000000000),((5821439:ℚ)/32000000)⟩
theorem valid22 : Valid tenth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound tenth nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4481:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC06
#check @N11Formalization.C450TenthGroupedC06.bound
#print axioms N11Formalization.C450TenthGroupedC06.valid0
#print axioms N11Formalization.C450TenthGroupedC06.valid1
#print axioms N11Formalization.C450TenthGroupedC06.valid2
#print axioms N11Formalization.C450TenthGroupedC06.valid3
#print axioms N11Formalization.C450TenthGroupedC06.valid4
#print axioms N11Formalization.C450TenthGroupedC06.valid5
#print axioms N11Formalization.C450TenthGroupedC06.valid6
#print axioms N11Formalization.C450TenthGroupedC06.valid7
#print axioms N11Formalization.C450TenthGroupedC06.valid8
#print axioms N11Formalization.C450TenthGroupedC06.valid9
#print axioms N11Formalization.C450TenthGroupedC06.valid10
#print axioms N11Formalization.C450TenthGroupedC06.valid11
#print axioms N11Formalization.C450TenthGroupedC06.valid12
#print axioms N11Formalization.C450TenthGroupedC06.valid13
#print axioms N11Formalization.C450TenthGroupedC06.valid14
#print axioms N11Formalization.C450TenthGroupedC06.valid15
#print axioms N11Formalization.C450TenthGroupedC06.valid16
#print axioms N11Formalization.C450TenthGroupedC06.valid17
#print axioms N11Formalization.C450TenthGroupedC06.valid18
#print axioms N11Formalization.C450TenthGroupedC06.valid19
#print axioms N11Formalization.C450TenthGroupedC06.valid20
#print axioms N11Formalization.C450TenthGroupedC06.valid21
#print axioms N11Formalization.C450TenthGroupedC06.valid22
#print axioms N11Formalization.C450TenthGroupedC06.bound
#print axioms N11Formalization.C450TenthGroupedC06.endpoint_checks
