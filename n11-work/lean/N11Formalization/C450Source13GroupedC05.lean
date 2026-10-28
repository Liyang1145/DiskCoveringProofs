import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((1623565289:ℚ)/2500000000),((678966611:ℚ)/1000000000),((-1860899833:ℚ)/2480000000),((-15939218179:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((341370821:ℚ)/625000000),((29332472042449297807387756412150669622162740052703954331:ℚ)/606821220480000000000000000000000000000000000000000000000),((10128391931598902682085987:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((841508187:ℚ)/1250000000),((6908558169:ℚ)/10000000000),((-18965674507:ℚ)/25750000000),((-8296590057:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2412926831:ℚ)/5000000000),((268358668435691080260348644759381674735758769942857892512763:ℚ)/5871278728159179687500000000000000000000000000000000000000000),((1013644719536513355212622267:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3425479691:ℚ)/5000000000),((6968002283:ℚ)/10000000000),((-19144006849:ℚ)/26225000000),((-33840276601:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1119267999:ℚ)/2500000000),((61552358777404028607895228988544993614559616064805775339633:ℚ)/1384125148516738281250000000000000000000000000000000000000000),((1014048190055365308881811283:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((1382080877:ℚ)/2000000000),((1405489033:ℚ)/2000000000),((-3864467099:ℚ)/5292500000),((-13666889647:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((107321157:ℚ)/250000000),((2512544198886613501678391050796160762943063191692073:ℚ)/56480660688476562500000000000000000000000000000000000),((112404668409155195159203:ℚ)/409600000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((348492407:ℚ)/500000000),((7086886849:ℚ)/10000000000),((-19500660547:ℚ)/26700000000),((-3449416477:ℚ)/5387500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2050445771:ℚ)/5000000000),((2304775052413184213481043761015240256092852317920773359201:ℚ)/51794020796528320312500000000000000000000000000000000000000),((1014856546749896262473581547:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((175732267:ℚ)/250000000),((7116607251:ℚ)/10000000000),((-19589821753:ℚ)/26937500000),((-1741054937:ℚ)/2705625000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3900062903:ℚ)/10000000000),((1256645379851132863850046488368327324084097880535930664739857:ℚ)/28617854051987285614013671875000000000000000000000000000000000),((1015058930989970610189886947:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((1411802301:ℚ)/2000000000),((1786581841:ℚ)/2500000000),((-4919745523:ℚ)/6764062500),((-13993825311:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((948970491:ℚ)/2500000000),((1446872515735665913615031660209982751101609929064786620541:ℚ)/32942681309014549255371093750000000000000000000000000000000),((63453839580987497630796107:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3544366019:ℚ)/5000000000),((3588023597:ℚ)/5000000000),((-9884070791:ℚ)/13587500000),((-35148026209:ℚ)/54587500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3688907339:ℚ)/10000000000),((164187214455119266522544288819268472103512147760768482441951:ℚ)/3737447367865229339599609375000000000000000000000000000000000),((253866013426200227924436323:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1779613071:ℚ)/2500000000),((7205766743:ℚ)/10000000000),((-19857300229:ℚ)/27293750000),((-5885247927:ℚ)/9137500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((894722003:ℚ)/2500000000),((149186286993639596278473314795889096532534571894870464796061:ℚ)/3395270682230494918823242187500000000000000000000000000000000),((1015666792227192047291445403:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((1429634449:ℚ)/2000000000),((1447097203:ℚ)/2000000000),((-3989291609:ℚ)/5482500000),((-14189978939:ℚ)/22025000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((54148961:ℚ)/156250000),((1756628336724521914114979740432578556180991905557013970449:ℚ)/39970332364278208007812500000000000000000000000000000000000),((40634785955475194425781923:ℚ)/147865600000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((287115677:ℚ)/400000000),((3632602507:ℚ)/5000000000),((-10017807521:ℚ)/13765625000),((-2851072447:ℚ)/4424000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((418563073:ℚ)/1250000000),((525964565845191339787854555217809088341661981843290457029487:ℚ)/11965457952024593353271484375000000000000000000000000000000000),((254018155926958873461024403:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7207611329:ℚ)/10000000000),((7294923743:ℚ)/10000000000),((-20124771229:ℚ)/27650000000),((-71603724619:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1613700503:ℚ)/5000000000),((5733208168959969025047548896689448956176965359063619761170189:ℚ)/130403141834448164062500000000000000000000000000000000000000000),((1016275716707258879831439403:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7237330459:ℚ)/10000000000),((1464928441:ℚ)/2000000000),((-4042785323:ℚ)/5553750000),((-71930635049:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3101744973:ℚ)/10000000000),((2929124277572677588717286188885716480449568862746452072137:ℚ)/66611336833089573211669921875000000000000000000000000000000),((40659157116095937786112507:ℚ)/147865600000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((181676233:ℚ)/250000000),((1470872081:ℚ)/2000000000),((-4060616243:ℚ)/5577500000),((-1806438563:ℚ)/2800625000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((1485479153:ℚ)/5000000000),((7661358946564885272089190868840968369655786803268853993027:ℚ)/174196180813001680468750000000000000000000000000000000000000),((40667290292969559058808267:ℚ)/147865600000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((3648383957:ℚ)/5000000000),((1476815669:ℚ)/2000000000),((-4078447007:ℚ)/5601250000),((-36292223527:ℚ)/56250000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((2834330241:ℚ)/10000000000),((12229599125034968609141752339669459295773028368821563:ℚ)/278016088406410217285156250000000000000000000000000000),((40675428199332085666517267:ℚ)/147865600000000000000000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3663243123:ℚ)/5000000000),((7443513459:ℚ)/10000000000),((-20570540377:ℚ)/28125000000),((-36455674353:ℚ)/56725000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2690970519:ℚ)/10000000000),((15950357035496243060481608577449550959424692715867808554913:ℚ)/357928769016265869140625000000000000000000000000000000000000),((1017292955096481017588639907:ℚ)/3696640000000000000000000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((1846480533:ℚ)/2500000000),((7502947573:ℚ)/10000000000),((-20748842719:ℚ)/28362500000),((-18391285863:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2379133611:ℚ)/10000000000),((25993531949554134163392788054279551864426465881329747705999:ℚ)/583197447626809082031250000000000000000000000000000000000000),((1017700678395541756053084563:ℚ)/3696640000000000000000000000)⟩
theorem valid16 : Valid source13 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3722678503:ℚ)/5000000000),((76218129:ℚ)/100000000),((-211054387:ℚ)/286000000),((-37109463533:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2020749591:ℚ)/10000000000),((164249383121650607756565375560939022182698323115155097:ℚ)/3595628852530000000000000000000000000000000000000000000),((14104813:ℚ)/51200000)⟩
theorem valid17 : Valid source13 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((945527977:ℚ)/1250000000),((3870337257:ℚ)/5000000000),((-10731011771:ℚ)/14537500000),((-9440807747:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((970679201:ℚ)/10000000000),((1701661931234195078259752438681822573281487658540365607491:ℚ)/37260755568434448242187500000000000000000000000000000000000),((14104813:ℚ)/51200000)⟩
theorem valid18 : Valid source13 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((480192929:ℚ)/625000000),((7978387299:ℚ)/10000000000),((-22175161897:ℚ)/29550000000),((-4802122219:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((17192306312506735635823216600464121479641224955107022510651:ℚ)/360050479308281250000000000000000000000000000000000000000000),((14104813:ℚ)/51200000)⟩
theorem valid19 : Valid source13 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((495050149:ℚ)/625000000),((8453775389:ℚ)/10000000000),((-23601326167:ℚ)/30500000000),((-4965551639:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((12007259441591524981531854510067781837411073179643558914687:ℚ)/232690990781250000000000000000000000000000000000000000000000),((14104813:ℚ)/51200000)⟩
theorem valid20 : Valid source13 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8396195461:ℚ)/10000000000),((2588739683:ℚ)/2500000000),((-7326219049:ℚ)/8100000000),((-84678150071:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((9080639405807773837452747946233779055452511588995873:ℚ)/124556484375000000000000000000000000000000000000000000),((14104813:ℚ)/51200000)⟩
theorem valid21 : Valid source13 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((5148697003:ℚ)/5000000000),((2831269469:ℚ)/2000000000),(-1:ℚ),((-52795667033:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((565927608595731365508976679:ℚ)/6094080000000000000000000000),((14104813:ℚ)/51200000)⟩
theorem valid22 : Valid source13 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source13 nn0 nn1 Qcell ((4367:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC05
#check @N11Formalization.C450Source13GroupedC05.bound
#print axioms N11Formalization.C450Source13GroupedC05.valid0
#print axioms N11Formalization.C450Source13GroupedC05.valid1
#print axioms N11Formalization.C450Source13GroupedC05.valid2
#print axioms N11Formalization.C450Source13GroupedC05.valid3
#print axioms N11Formalization.C450Source13GroupedC05.valid4
#print axioms N11Formalization.C450Source13GroupedC05.valid5
#print axioms N11Formalization.C450Source13GroupedC05.valid6
#print axioms N11Formalization.C450Source13GroupedC05.valid7
#print axioms N11Formalization.C450Source13GroupedC05.valid8
#print axioms N11Formalization.C450Source13GroupedC05.valid9
#print axioms N11Formalization.C450Source13GroupedC05.valid10
#print axioms N11Formalization.C450Source13GroupedC05.valid11
#print axioms N11Formalization.C450Source13GroupedC05.valid12
#print axioms N11Formalization.C450Source13GroupedC05.valid13
#print axioms N11Formalization.C450Source13GroupedC05.valid14
#print axioms N11Formalization.C450Source13GroupedC05.valid15
#print axioms N11Formalization.C450Source13GroupedC05.valid16
#print axioms N11Formalization.C450Source13GroupedC05.valid17
#print axioms N11Formalization.C450Source13GroupedC05.valid18
#print axioms N11Formalization.C450Source13GroupedC05.valid19
#print axioms N11Formalization.C450Source13GroupedC05.valid20
#print axioms N11Formalization.C450Source13GroupedC05.valid21
#print axioms N11Formalization.C450Source13GroupedC05.valid22
#print axioms N11Formalization.C450Source13GroupedC05.bound
#print axioms N11Formalization.C450Source13GroupedC05.endpoint_checks
