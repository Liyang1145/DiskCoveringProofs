import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3477672791:ℚ)/5000000000),((3556841211:ℚ)/5000000000),((-9262523633:ℚ)/9920000000),((-20663709537:ℚ)/25037500000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((4148493513:ℚ)/10000000000),((16039615935329156033171309478869841599543267:ℚ)/61195141180928000000000000000000000000000000),((70840235113381344342177:ℚ)/81920000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1402971983:ℚ)/2000000000),((896641813:ℚ)/1250000000),((-2337925439:ℚ)/2503750000),((-2782934627:ℚ)/3370000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((3949705841:ℚ)/10000000000),((1823283981460182483112899756938985012115963648251600497:ℚ)/6962941130007652282714843750000000000000000000000000000),((1603404601422815286661033:ℚ)/1848320000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7074371621:ℚ)/10000000000),((7202860003:ℚ)/10000000000),((-18792580009:ℚ)/20220000000),((-42160601347:ℚ)/50787500000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((1870479739:ℚ)/5000000000),((6832814430604655971245185276853874868893293794402118632851781:ℚ)/26654291159146467187500000000000000000000000000000000000000000),((102780375266165519335552313:ℚ)/118292480000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7104126511:ℚ)/10000000000),((1808146287:ℚ)/2500000000),((-4720438861:ℚ)/5078750000),((-42368885577:ℚ)/51025000000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((1816158579:ℚ)/5000000000),((7757674537068264657673758757491861767974716700838446519747:ℚ)/30271998083139093017578125000000000000000000000000000000000),((6433936141436783245426833:ℚ)/7393280000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((8183:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1783470193:ℚ)/2500000000),((7247447589:ℚ)/10000000000),((-18926342767:ℚ)/20410000000),((-10644291351:ℚ)/12785937500),((9888211123:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((37416203:ℚ)/250000000),((440059877:ℚ)/1250000000),((84989076050910732044339727006061957812133234460329202661517:ℚ)/335155192240288875000000000000000000000000000000000000000000),((103024325600000980198490697:ℚ)/118292480000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8183:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((8183:ℚ)/12800),((4101:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((714875767:ℚ)/1000000000),((907788743:ℚ)/1250000000),((-2371366229:ℚ)/2557187500),((-1422710123:ℚ)/1708750000),((4940065779:ℚ)/5000000000),((1236026391:ℚ)/1250000000),((774947369:ℚ)/5000000000),((1731632467:ℚ)/5000000000),((11842730745007361430505992411122756331322786573669466449:ℚ)/46707860497294680029153823852539062500000000000000000000),((1611026617257435419682593:ℚ)/1848320000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((8183:ℚ)/12800) ((4101:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7163634413:ℚ)/10000000000),((1819293053:ℚ)/2500000000),((-4753879159:ℚ)/5126250000),((-42785440891:ℚ)/51381250000),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((170256481:ℚ)/500000000),((7212828739373479695261218050970711581123033643412368590586219:ℚ)/28451073983482416632080078125000000000000000000000000000000000),((6449194498149738881457913:ℚ)/7393280000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((7178511003:ℚ)/10000000000),((1458406879:ℚ)/2000000000),((-3812020637:ℚ)/4110500000),((-42889577021:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((1673012491:ℚ)/5000000000),((583661173713282667490049349826085748690161354149104272393:ℚ)/2302546601612245703125000000000000000000000000000000000000),((4130742040327084109954737:ℚ)/4731699200000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7193387441:ℚ)/10000000000),((1826724123:ℚ)/2500000000),((-4776172369:ℚ)/5150000000),((-42993712087:ℚ)/51618750000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((3285898643:ℚ)/10000000000),((9608676167986984644411959793117142671829656687699393640807:ℚ)/37911015781599426269531250000000000000000000000000000000000),((6459376288237777098846153:ℚ)/7393280000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((450516483:ℚ)/625000000),((3660879253:ℚ)/5000000000),((-9574637759:ℚ)/10323750000),((-2693615381:ℚ)/3233593750),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((1612346691:ℚ)/5000000000),((3731964928719484764311321334643967069108235112631887637518979:ℚ)/14726289046257507719421386718750000000000000000000000000000000),((25857880199298382903398313:ℚ)/29573120000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3611569933:ℚ)/5000000000),((1467324087:ℚ)/2000000000),((-3838772261:ℚ)/4139000000),((-21600989531:ℚ)/25928125000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((790586619:ℚ)/2500000000),((154606993424552147183550617362648908443490580217024057473601:ℚ)/610152608644790296375000000000000000000000000000000000000000),((4140522062114022282247233:ℚ)/4731699200000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3619007927:ℚ)/5000000000),((7351482281:ℚ)/10000000000),((-19238446843:ℚ)/20742500000),((-7217685163:ℚ)/8662500000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((61975779:ℚ)/200000000),((13465939713749254075243954172909432495196723282291615381769:ℚ)/53149507725567370605468750000000000000000000000000000000000),((103594612889221015536350977:ℚ)/118292480000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((1450578339:ℚ)/2000000000),((1473268809:ℚ)/2000000000),((-3856606427:ℚ)/4158000000),((-8682048373:ℚ)/10418750000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((1516972319:ℚ)/5000000000),((97802319910206165711533442580599213291362205885566259631:ℚ)/386068756186575000000000000000000000000000000000000000000),((4147048192451040860119617:ℚ)/4731699200000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7267767389:ℚ)/10000000000),((7381205727:ℚ)/10000000000),((-19327617181:ℚ)/20837500000),((-43514371723:ℚ)/52212500000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((18548307:ℚ)/62500000),((124953294489731992987318133219402360351333668721307372745500721:ℚ)/493305333207280438232421875000000000000000000000000000000000000),((103757827318501856623051953:ℚ)/118292480000000000000000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3641321469:ℚ)/5000000000),((7396067327:ℚ)/10000000000),((-19372201981:ℚ)/20885000000),((-21809250283:ℚ)/26165625000),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((290004839:ℚ)/1000000000),((505469853087695818013929179325685401621470538365988326256871489:ℚ)/1995793679407249241015625000000000000000000000000000000000000000),((103839480410384805397936753:ℚ)/118292480000000000000000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7297518341:ℚ)/10000000000),((3705464423:ℚ)/5000000000),((-9708393269:ℚ)/10466250000),((-43722628387:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((707699321:ℚ)/2500000000),((2995181939191548893874103360038599822072327240079662418019907:ℚ)/11827571045510337835693359375000000000000000000000000000000000),((25980291022977130115222753:ℚ)/29573120000000000000000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((7312393601:ℚ)/10000000000),((7440651643:ℚ)/10000000000),((-19505954929:ℚ)/20980000000),((-43826755207:ℚ)/52687500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((1103943:ℚ)/4000000),((5244060370173927356226372624951076527259721057861290094847949:ℚ)/20507920372280025000000000000000000000000000000000000000000000),((104084623232851555310288393:ℚ)/118292480000000000000000000)⟩
theorem valid16 : Valid source24 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source24 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7342143693:ℚ)/10000000000),((7470374123:ℚ)/10000000000),((-19595122369:ℚ)/21075000000),((-44035005851:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((163272379:ℚ)/625000000),((4021550133016099843558935680320351125863439317140247752273183:ℚ)/15731702815978845703125000000000000000000000000000000000000000),((104248204764825082976746153:ℚ)/118292480000000000000000000)⟩
theorem valid17 : Valid source24 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source24 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((7371893221:ℚ)/10000000000),((1882454537:ℚ)/2500000000),((-4943363611:ℚ)/5292500000),((-14747750849:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((491246609:ℚ)/2000000000),((716908622616546423114816116373285423987178134240751523773:ℚ)/2752161393697741699218750000000000000000000000000000000000),((6535983442137604664912833:ℚ)/7393280000000000000000000)⟩
theorem valid18 : Valid source24 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3715695309:ℚ)/5000000000),((1912175643:ℚ)/2500000000),((-5032526929:ℚ)/5340000000),((-22329867163:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1055176909:ℚ)/5000000000),((455397201478606643157129549355774808406142623824718407128423:ℚ)/1686763270631025000000000000000000000000000000000000000000000),((908613823:ℚ)/1024000000)⟩
theorem valid19 : Valid source24 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((3775189487:ℚ)/5000000000),((776758237:ℚ)/1000000000),((-2048674711:ℚ)/2174000000),((-22746326409:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1143345933:ℚ)/10000000000),((896755368495480487840923750265389087010496463113274721:ℚ)/3329316202307812500000000000000000000000000000000000000),((908613823:ℚ)/1024000000)⟩
theorem valid20 : Valid source24 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((1917339779:ℚ)/2500000000),((8005329011:ℚ)/10000000000),((-21199987033:ℚ)/22120000000),((-11581378453:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((4052822081848725732046598065781774474511998458713050420253:ℚ)/14115016315400000000000000000000000000000000000000000000000),((908613823:ℚ)/1024000000)⟩
theorem valid21 : Valid source24 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((1976824101:ℚ)/2500000000),((1791234151:ℚ)/2000000000),(-1:ℚ),((-11997768707:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((229612513685205422208099635743213703:ℚ)/656100000000000000000000000000000000),((908613823:ℚ)/1024000000)⟩
theorem valid22 : Valid source24 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((1771757707:ℚ)/2000000000),((10857374001:ℚ)/10000000000),(-1:ℚ),((-10930303949:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((178501327414121868917511719000292809:ℚ)/480000000000000000000000000000000000),((908613823:ℚ)/1024000000)⟩
theorem valid23 : Valid source24 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((2690230219:ℚ)/2500000000),((14658785961:ℚ)/10000000000),(-1:ℚ),((-5663870511:ℚ)/9200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8681893744101209640718553:ℚ)/21160000000000000000000000),((908613823:ℚ)/1024000000)⟩
theorem valid24 : Valid source24 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet24 valid24
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((2003:ℚ)/3200) ((4063:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((4063:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source24 nn0 nn1 Qcell ((4063:ℚ)/6400) ((4101:ℚ)/6400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((8221:ℚ)/12800) ((8259:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8259:ℚ)/12800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source24 nn0 nn1 Qcell ((8259:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source24 nn0 nn1 Qcell ((4101:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source24 nn0 nn1 Qcell ((1667:ℚ)/2560) ((8373:ℚ)/12800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((8373:ℚ)/12800) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source24 nn0 nn1 Qcell ((8373:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf18 node19_21
private theorem node21_23 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node21_23 node23_25
private theorem node18_25 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node18_21 node21_25
private theorem node12_25 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node12_18 node18_25
private theorem node0_25 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_25
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_25
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24]
theorem packet_count : packets.length = 25 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC02
#check @N11Formalization.C450Source24GroupedC02.bound
#print axioms N11Formalization.C450Source24GroupedC02.valid0
#print axioms N11Formalization.C450Source24GroupedC02.valid1
#print axioms N11Formalization.C450Source24GroupedC02.valid2
#print axioms N11Formalization.C450Source24GroupedC02.valid3
#print axioms N11Formalization.C450Source24GroupedC02.valid4
#print axioms N11Formalization.C450Source24GroupedC02.valid5
#print axioms N11Formalization.C450Source24GroupedC02.valid6
#print axioms N11Formalization.C450Source24GroupedC02.valid7
#print axioms N11Formalization.C450Source24GroupedC02.valid8
#print axioms N11Formalization.C450Source24GroupedC02.valid9
#print axioms N11Formalization.C450Source24GroupedC02.valid10
#print axioms N11Formalization.C450Source24GroupedC02.valid11
#print axioms N11Formalization.C450Source24GroupedC02.valid12
#print axioms N11Formalization.C450Source24GroupedC02.valid13
#print axioms N11Formalization.C450Source24GroupedC02.valid14
#print axioms N11Formalization.C450Source24GroupedC02.valid15
#print axioms N11Formalization.C450Source24GroupedC02.valid16
#print axioms N11Formalization.C450Source24GroupedC02.valid17
#print axioms N11Formalization.C450Source24GroupedC02.valid18
#print axioms N11Formalization.C450Source24GroupedC02.valid19
#print axioms N11Formalization.C450Source24GroupedC02.valid20
#print axioms N11Formalization.C450Source24GroupedC02.valid21
#print axioms N11Formalization.C450Source24GroupedC02.valid22
#print axioms N11Formalization.C450Source24GroupedC02.valid23
#print axioms N11Formalization.C450Source24GroupedC02.valid24
#print axioms N11Formalization.C450Source24GroupedC02.bound
#print axioms N11Formalization.C450Source24GroupedC02.endpoint_checks
