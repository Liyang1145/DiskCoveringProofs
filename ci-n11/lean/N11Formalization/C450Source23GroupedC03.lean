import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((6863131539:ℚ)/10000000000),((3537185813:ℚ)/5000000000),((-21400300691:ℚ)/24800000000),((-75140710007:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((554991411:ℚ)/1250000000),((581590655876172590188509267753265536276865456645281617121803:ℚ)/2706667263200000000000000000000000000000000000000000000000000),((40430971533426028695107457:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1745561661:ℚ)/2500000000),((7133880777:ℚ)/10000000000),((-42746949:ℚ)/50000000),((-19172301593:ℚ)/25512500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((162391143:ℚ)/400000000),((623734332281651971294411690182509389519014643173:ℚ)/3008911132812500000000000000000000000000000000000),((486209917289182820905443211:ℚ)/693120000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1760449769:ℚ)/2500000000),((3581817209:ℚ)/5000000000),((-21712720463:ℚ)/25512500000),((-19365846997:ℚ)/25631250000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((771308579:ℚ)/2000000000),((2468109822489520813399198094765465212684540366766529371161559:ℚ)/12121493055090766143798828125000000000000000000000000000000000),((40560761578840711500471993:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((7071574053:ℚ)/10000000000),((3596693723:ℚ)/5000000000),((-21816856061:ℚ)/25631250000),((-77850462689:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((937754913:ℚ)/2500000000),((56831622449483264179584650934315450011326539137990970116797:ℚ)/279128277348064041137695312500000000000000000000000000000000),((40604035187227128482728737:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((355067411:ℚ)/500000000),((7223139871:ℚ)/10000000000),((-43841979097:ℚ)/51500000000),((-3911876343:ℚ)/5173750000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((182129613:ℚ)/500000000),((7443824658958395684740987057903563906648231394237023732054129:ℚ)/36562220707748046875000000000000000000000000000000000000000000),((162589255787063426482284873:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7131121587:ℚ)/10000000000),((7238015859:ℚ)/10000000000),((-43946111013:ℚ)/51737500000),((-78624580631:ℚ)/103712500000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((441374081:ℚ)/1250000000),((3006074375072113354051090418263393268269388125699906958053360101:ℚ)/14896303921991950595092773437500000000000000000000000000000000000),((488027463125602824816509779:ℚ)/693120000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((285840319:ℚ)/400000000),((72528917:ℚ)/100000000),((-440502419:ℚ)/518562500),((-116767561:ℚ)/154000000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((868476971:ℚ)/2500000000),((9310388097963742383187995560699447563438285030238639:ℚ)/46136725456221675872802734375000000000000000000000000),((16276239146909964417217:ℚ)/23104000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((7160894167:ℚ)/10000000000),((3633883697:ℚ)/5000000000),((-3153883697:ℚ)/3712500000),((-79011624171:ℚ)/104187500000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((1707954671:ℚ)/5000000000),((1018963359825305993803080892562875605381587549118319883459:ℚ)/5049378612233734130859375000000000000000000000000000000000),((40712241767145209364495977:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1435156033:ℚ)/2000000000),((7282642943:ℚ)/10000000000),((-44258500601:ℚ)/52093750000),((-15841028429:ℚ)/20885000000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((839237397:ℚ)/2500000000),((194431170632410345403680857118501036309236781839407351807321857:ℚ)/963486978920469605922698974609375000000000000000000000000000000),((451345007899649812876577:ℚ)/640000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7190665969:ℚ)/10000000000),((3648759173:ℚ)/5000000000),((-22181314211:ℚ)/26106250000),((-26466219199:ℚ)/34887500000),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((659395397:ℚ)/2000000000),((10925276389623312017202067394248890011826225490694427955258483:ℚ)/54139368473503939914703369140625000000000000000000000000000000),((40755533453170166823098337:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3602775791:ℚ)/5000000000),((3656196803:ℚ)/5000000000),((-22233377621:ℚ)/26165625000),((-39796085283:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((161796757:ℚ)/500000000),((517966110457449329543920878376778151323133672707147989318799:ℚ)/2566747188695819842815399169921875000000000000000000000000000),((40777181242147170298944977:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((1444087401:ℚ)/2000000000),((7327268723:ℚ)/10000000000),((-44570881061:ℚ)/52450000000),((-15957136213:ℚ)/21027500000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((793440571:ℚ)/2500000000),((19045050015097502007913044091110791940603369308965399133125957:ℚ)/94376760265086132812500000000000000000000000000000000000000000),((163195321319323796719578737:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((3617661119:ℚ)/5000000000),((3671071849:ℚ)/5000000000),((-22337502943:ℚ)/26284375000),((-13329864849:ℚ)/17562500000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((3110390527:ℚ)/10000000000),((4521070550519031809165852047828738794131155104379527813551:ℚ)/22404003394250054836273193359375000000000000000000000000000),((40820480717633588373843353:ℚ)/57760000000000000000000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((1812551821:ℚ)/2500000000),((1839254633:ℚ)/2500000000),((-11194782431:ℚ)/13171875000),((-20043173673:ℚ)/26403125000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((3045744947:ℚ)/10000000000),((4286533863739487623687103569643291619118090892166859313270149:ℚ)/21241843366889311373233795166015625000000000000000000000000000),((10210533101741894596742617:ℚ)/14440000000000000000000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7265092143:ℚ)/10000000000),((3685946613:ℚ)/5000000000),((-3205946613:ℚ)/3771875000),((-80366197859:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1489871283:ℚ)/5000000000),((4460637769607494925635211720038313049152736755605710249357:ℚ)/22104703607331800460815429687500000000000000000000000000000),((122591356197737445942309571:ℚ)/173280000000000000000000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3639988409:ℚ)/5000000000),((7401642199:ℚ)/10000000000),((-45091495393:ℚ)/52925000000),((-40279849317:ℚ)/53162500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((2912291049:ℚ)/10000000000),((852728158122892341836383088716870186193161708446812117458136489:ℚ)/4189800955995227465820312500000000000000000000000000000000000000),((163628381198978354801433753:ℚ)/231040000000000000000000000)⟩
theorem valid15 : Valid source23 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((1461949123:ℚ)/2000000000),((7431390623:ℚ)/10000000000),((-45299734361:ℚ)/53162500000),((-16189338599:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((1386307503:ℚ)/5000000000),((94612243772519871120744266232118037667590739182642116469233:ℚ)/464896455639737701416015625000000000000000000000000000000000),((163801641710117992938340937:ℚ)/231040000000000000000000000)⟩
theorem valid16 : Valid source23 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source23 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((3669756843:ℚ)/5000000000),((1498177171:ℚ)/2000000000),((-9143240197:ℚ)/10680000000),((-40666838959:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1312861663:ℚ)/5000000000),((285772938712854277207432446497862290882878934380395960149:ℚ)/1381173887907421875000000000000000000000000000000000000000),((6565929025404208796154673:ℚ)/9241600000000000000000000)⟩
theorem valid17 : Valid source23 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7399047689:ℚ)/10000000000),((7550378979:ℚ)/10000000000),((-46132652853:ℚ)/53875000000),((-82107619957:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((115235507:ℚ)/500000000),((59714361565145201056809686174105462155111857967855637332615629:ℚ)/288696131020748901367187500000000000000000000000000000000000000),((493484681080817459443456819:ℚ)/693120000000000000000000000)⟩
theorem valid18 : Valid source23 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((7458578901:ℚ)/10000000000),((7669359121:ℚ)/10000000000),((-46965513847:ℚ)/54350000000),((-11840217959:ℚ)/15800000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((386430199:ℚ)/2000000000),((5219888085377425275951043154225127984367275665528658534511:ℚ)/24462051709664916992187500000000000000000000000000000000000),((5705821:ℚ)/8000000)⟩
theorem valid19 : Valid source23 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((1515526649:ℚ)/2000000000),((7907296409:ℚ)/10000000000),((-6947296409:ℚ)/7900000000),((-16885846437:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((383695111:ℚ)/5000000000),((21063071622190621985507267114563410005856551091105617257:ℚ)/93215185937500000000000000000000000000000000000000000000),((5705821:ℚ)/8000000)⟩
theorem valid20 : Valid source23 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((3907855747:ℚ)/5000000000),((442939427:ℚ)/500000000),((-2764575989:ℚ)/2860000000),((-43762124711:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((20035021962394746510962455244210430887823828492924103:ℚ)/67289990625000000000000000000000000000000000000000000),((5705821:ℚ)/8000000)⟩
theorem valid21 : Valid source23 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((1753536873:ℚ)/2000000000),((10760920881:ℚ)/10000000000),(-1:ℚ),((-19979979349:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13312918847081934916981649661999727:ℚ)/40000000000000000000000000000000000),((5705821:ℚ)/8000000)⟩
theorem valid22 : Valid source23 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((5335251557:ℚ)/5000000000),((3640855587:ℚ)/2500000000),(-1:ℚ),((-20772756747:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((7683525349444034757572933:ℚ)/21160000000000000000000000),((5705821:ℚ)/8000000)⟩
theorem valid23 : Valid source23 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet23 valid23
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4101:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((8297:ℚ)/12800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((8297:ℚ)/12800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((8297:ℚ)/12800) ((4177:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((8373:ℚ)/12800) ((8411:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source23 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8411:ℚ)/12800) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source23 nn0 nn1 Qcell ((8297:ℚ)/12800) ((8411:ℚ)/12800) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((8411:ℚ)/12800) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source23 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source23 nn0 nn1 Qcell ((8411:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source23 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source23 nn0 nn1 Qcell ((8411:ℚ)/12800) ((431:ℚ)/640) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((143:ℚ)/200) :=
  cell_join leaf18 node19_21
private theorem node22_24 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf21 node22_24
private theorem node18_24 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node18_21 node21_24
private theorem node12_24 :
    CellBound source23 nn0 nn1 Qcell ((8411:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node12_18 node18_24
private theorem node0_24 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_24
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_24
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23]
theorem packet_count : packets.length = 24 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC03
#check @N11Formalization.C450Source23GroupedC03.bound
#print axioms N11Formalization.C450Source23GroupedC03.valid0
#print axioms N11Formalization.C450Source23GroupedC03.valid1
#print axioms N11Formalization.C450Source23GroupedC03.valid2
#print axioms N11Formalization.C450Source23GroupedC03.valid3
#print axioms N11Formalization.C450Source23GroupedC03.valid4
#print axioms N11Formalization.C450Source23GroupedC03.valid5
#print axioms N11Formalization.C450Source23GroupedC03.valid6
#print axioms N11Formalization.C450Source23GroupedC03.valid7
#print axioms N11Formalization.C450Source23GroupedC03.valid8
#print axioms N11Formalization.C450Source23GroupedC03.valid9
#print axioms N11Formalization.C450Source23GroupedC03.valid10
#print axioms N11Formalization.C450Source23GroupedC03.valid11
#print axioms N11Formalization.C450Source23GroupedC03.valid12
#print axioms N11Formalization.C450Source23GroupedC03.valid13
#print axioms N11Formalization.C450Source23GroupedC03.valid14
#print axioms N11Formalization.C450Source23GroupedC03.valid15
#print axioms N11Formalization.C450Source23GroupedC03.valid16
#print axioms N11Formalization.C450Source23GroupedC03.valid17
#print axioms N11Formalization.C450Source23GroupedC03.valid18
#print axioms N11Formalization.C450Source23GroupedC03.valid19
#print axioms N11Formalization.C450Source23GroupedC03.valid20
#print axioms N11Formalization.C450Source23GroupedC03.valid21
#print axioms N11Formalization.C450Source23GroupedC03.valid22
#print axioms N11Formalization.C450Source23GroupedC03.valid23
#print axioms N11Formalization.C450Source23GroupedC03.bound
#print axioms N11Formalization.C450Source23GroupedC03.endpoint_checks
