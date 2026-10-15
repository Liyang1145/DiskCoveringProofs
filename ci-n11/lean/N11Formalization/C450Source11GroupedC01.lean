import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((6536234243:ℚ)/10000000000),((6837500003:ℚ)/10000000000),(-1:ℚ),((-18328702729:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5354662521:ℚ)/10000000000),((21708651681396451499192077394966369:ℚ)/530450000000000000000000000000000000),((515839548538581174250856003:ℚ)/1478656000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((135475619:ℚ)/200000000),((6956250003:ℚ)/10000000000),(-1:ℚ),((-380826857:ℚ)/419600000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4706207947:ℚ)/10000000000),((4296175009024412213801960194421:ℚ)/110040100000000000000000000000000),((206911138951727124820867:ℚ)/591462400000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3446276517:ℚ)/5000000000),((7015625003:ℚ)/10000000000),(-1:ℚ),((-9698829551:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2174468029:ℚ)/5000000000),((5340498145423393374291331115084841:ℚ)/140052781250000000000000000000000000),((129498850983409682872015283:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((6951938779:ℚ)/10000000000),((7045312503:ℚ)/10000000000),(-1:ℚ),((-19575816337:ℚ)/21265000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1039900309:ℚ)/2500000000),((63903689430034459100412048702048143:ℚ)/1695750843750000000000000000000000000),((518353783993555978179803827:ℚ)/1478656000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((6981631579:ℚ)/10000000000),((3537500001:ℚ)/5000000000),(-1:ℚ),((-19664894737:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((4061827367:ℚ)/10000000000),((10742752292568174233986232082114311:ℚ)/285156000000000000000000000000000000),((518727542984331398298376627:ℚ)/1478656000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1752831083:ℚ)/2500000000),((3552343751:ℚ)/5000000000),(-1:ℚ),((-4938493249:ℚ)/5363750000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3961778571:ℚ)/10000000000),((32505942216290976035028418694173603:ℚ)/863094421875000000000000000000000000),((32443827226160656950870483:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((7041017039:ℚ)/10000000000),((7134375003:ℚ)/10000000000),(-1:ℚ),((-19843051117:ℚ)/21550000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1929638731:ℚ)/5000000000),((8196224956106833883511044227732021:ℚ)/217688671875000000000000000000000000),((519474861896058368083851787:ℚ)/1478656000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7070709699:ℚ)/10000000000),((111706543:ℚ)/156250000),(-1:ℚ),((-19932129097:ℚ)/21597500000),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((3754122711:ℚ)/10000000000),((267807980434670016231050089375111:ℚ)/7154171875000000000000000000000000),((519653753250292475073860547:ℚ)/1478656000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7085556013:ℚ)/10000000000),((3582031251:ℚ)/5000000000),(-1:ℚ),((-539909947:ℚ)/585000000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((925119899:ℚ)/2500000000),((8005745421770700555818904651551:ℚ)/213890625000000000000000000000000),((519840508308813961463868643:ℚ)/1478656000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1420080463:ℚ)/2000000000),((1794726563:ℚ)/2500000000),(-1:ℚ),((-4004241389:ℚ)/4338500000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((1823042119:ℚ)/5000000000),((5283197491224543202442541930769513:ℚ)/141169366875000000000000000000000000),((1094794203737531660153897:ℚ)/3112960000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((3557624303:ℚ)/5000000000),((3596875001:ℚ)/5000000000),(-1:ℚ),((-10032872909:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((897725597:ℚ)/2500000000),((5526781518187517788371976796028261:ℚ)/147696125000000000000000000000000000),((130053492162334408513083723:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((3565047443:ℚ)/5000000000),((7208593753:ℚ)/10000000000),(-1:ℚ),((-10055142329:ℚ)/10893750000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((3534897153:ℚ)/10000000000),((792897873930364225345530811578851:ℚ)/21191748046875000000000000000000000),((130100168485998913437410403:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3572470577:ℚ)/5000000000),((7223437503:ℚ)/10000000000),(-1:ℚ),((-10077411731:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((3478028699:ℚ)/10000000000),((2786920751381099207551910426878967:ℚ)/74494878906250000000000000000000000),((130146840658411881586084363:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1789946853:ℚ)/2500000000),((1809570313:ℚ)/2500000000),(-1:ℚ),((-5049840559:ℚ)/5470625000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((3420253897:ℚ)/10000000000),((8955921043237307166348286966176053:ℚ)/239421903125000000000000000000000000),((32548377169828446900310323:ℚ)/92416000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7174633659:ℚ)/10000000000),((3626562501:ℚ)/5000000000),(-1:ℚ),((-20243900977:ℚ)/21930000000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((672305191:ℚ)/2000000000),((11242225101058304708570443276990009:ℚ)/300578062500000000000000000000000000),((520960690221621381983035507:ℚ)/1478656000000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1437895979:ℚ)/2000000000),((454248047:ℚ)/625000000),(-1:ℚ),((-4057687937:ℚ)/4395500000),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((3301793949:ℚ)/10000000000),((1806344697651061301714105018440983:ℚ)/48301050625000000000000000000000000),((20845893165346744163891027:ℚ)/59146240000000000000000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((180108153:ℚ)/250000000),((3641406251:ℚ)/5000000000),(-1:ℚ),((-508324459:ℚ)/550625000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((1620501149:ℚ)/5000000000),((113371890482025019081440717053233:ℚ)/3031878906250000000000000000000000),((325833719658396069436923:ℚ)/924160000000000000000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1443834467:ℚ)/2000000000),((7297656253:ℚ)/10000000000),(-1:ℚ),((-4075503401:ℚ)/4414500000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((99346567:ℚ)/312500000),((607190886786365789662779512099131:ℚ)/16239841875000000000000000000000000),((20860822287740978467226883:ℚ)/59146240000000000000000000)⟩
theorem valid17 : Valid source11 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((7234018539:ℚ)/10000000000),((7312500003:ℚ)/10000000000),(-1:ℚ),((-20422055617:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3115990631:ℚ)/10000000000),((408306234488717270290443490288119:ℚ)/10921750000000000000000000000000000),((521707146328290138394200787:ℚ)/1478656000000000000000000000)⟩
theorem valid18 : Valid source11 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source11 nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1812216183:ℚ)/2500000000),((7327343753:ℚ)/10000000000),(-1:ℚ),((-5116648549:ℚ)/5541875000),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((1525815019:ℚ)/5000000000),((45921701324194253552423625510886569:ℚ)/1228495140625000000000000000000000000),((32618357429430134179470683:ℚ)/92416000000000000000000000)⟩
theorem valid19 : Valid source11 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1815927729:ℚ)/2500000000),((3671093751:ℚ)/5000000000),(-1:ℚ),((-5127783187:ℚ)/5553750000),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((2985926739:ℚ)/10000000000),((1280931264582618542497332704559369:ℚ)/34271265625000000000000000000000000),((32630017175445554248054027:ℚ)/92416000000000000000000000)⟩
theorem valid20 : Valid source11 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source11 nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((227454909:ℚ)/312500000),((3685937501:ℚ)/5000000000),(-1:ℚ),((-642364727:ℚ)/697187500),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1459395001:ℚ)/5000000000),((2921854825380000641221234335013761:ℚ)/77771265625000000000000000000000000),((26853489036437801585553:ℚ)/76000000000000000000000)⟩
theorem valid21 : Valid source11 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3654124701:ℚ)/5000000000),((7401562503:ℚ)/10000000000),(-1:ℚ),((-10322374103:ℚ)/11202500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((138989913:ℚ)/500000000),((2356841808852497030886194909474251:ℚ)/62748003125000000000000000000000000),((130708627910962135666534147:ℚ)/369664000000000000000000000)⟩
theorem valid22 : Valid source11 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),(-1:ℚ),((-15:ℚ)/16),((1834485419:ℚ)/2500000000),((3715625001:ℚ)/5000000000),(-1:ℚ),((-5183456257:ℚ)/5625000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((2633680379:ℚ)/10000000000),((61882396125074524811595750764261:ℚ)/1647949218750000000000000000000000),((32700467137396542599811667:ℚ)/92416000000000000000000000)⟩
theorem valid23 : Valid source11 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7367633909:ℚ)/10000000000),((7490625003:ℚ)/10000000000),(-1:ℚ),((-20822901727:ℚ)/22690000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2479176011:ℚ)/10000000000),((1220359507143426979701689130847497:ℚ)/32177256250000000000000000000000000),((523969707465703477686559507:ℚ)/1478656000000000000000000000)⟩
theorem valid24 : Valid source11 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((464188641:ℚ)/625000000),((7550000003:ℚ)/10000000000),(-1:ℚ),((-1312565923:ℚ)/1430000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((66801399:ℚ)/312500000),((96887027730065129148807969236151:ℚ)/2556125000000000000000000000000000),((2049669143566233857649707:ℚ)/5776000000000000000000000)⟩
theorem valid25 : Valid source11 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((467900153:ℚ)/625000000),((7787500003:ℚ)/10000000000),(-1:ℚ),((-1323700459:ℚ)/1477500000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1731151709:ℚ)/10000000000),((27303314959350309599933291003587:ℚ)/682189453125000000000000000000000),((2052100312412460476380923:ℚ)/5776000000000000000000000)⟩
theorem valid26 : Valid source11 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(-1:ℚ),((-15:ℚ)/16),((3861968869:ℚ)/5000000000),((4012500001:ℚ)/5000000000),(-1:ℚ),((-10945906607:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((22244228359669110227614854894443153:ℚ)/558150000000000000000000000000000000),((36376257:ℚ)/102400000)⟩
theorem valid27 : Valid source11 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((796147083:ℚ)/1000000000),((8500000003:ℚ)/10000000000),(-1:ℚ),((-2260441249:ℚ)/2592000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((353562253153980100675405892652421:ℚ)/8398080000000000000000000000000000),((36376257:ℚ)/102400000)⟩
theorem valid28 : Valid source11 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((843653119:ℚ)/1000000000),((5200000001:ℚ)/5000000000),(-1:ℚ),((-2402959357:ℚ)/3200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1988325413849481105112058002394333:ℚ)/38400000000000000000000000000000000),((36376257:ℚ)/102400000)⟩
theorem valid29 : Valid source11 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((10336715279:ℚ)/10000000000),((14200000003:ℚ)/10000000000),(-1:ℚ),((-29730145837:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((14346263432650278226757131:ℚ)/243763200000000000000000000),((36376257:ℚ)/102400000)⟩
theorem valid30 : Valid source11 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet30 valid30
private theorem node1_3 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source11 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source11 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source11 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source11 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source11 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_7 node7_15
private theorem node15_17 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_join leaf15 leaf16
private theorem node17_19 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_join leaf17 leaf18
private theorem node15_19 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join node15_17 node17_19
private theorem node19_21 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_join leaf19 leaf20
private theorem node21_23 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf21 leaf22
private theorem node19_23 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join node19_21 node21_23
private theorem node15_23 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_join node15_19 node19_23
private theorem node23_25 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join node23_25 node25_27
private theorem node27_29 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf27 leaf28
private theorem node29_31 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf29 leaf30
private theorem node27_31 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node27_29 node29_31
private theorem node23_31 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node23_27 node27_31
private theorem node15_31 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_23 node23_31
private theorem node0_31 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_31
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_31
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30]
theorem packet_count : packets.length = 31 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC01
#check @N11Formalization.C450Source11GroupedC01.bound
#print axioms N11Formalization.C450Source11GroupedC01.valid0
#print axioms N11Formalization.C450Source11GroupedC01.valid1
#print axioms N11Formalization.C450Source11GroupedC01.valid2
#print axioms N11Formalization.C450Source11GroupedC01.valid3
#print axioms N11Formalization.C450Source11GroupedC01.valid4
#print axioms N11Formalization.C450Source11GroupedC01.valid5
#print axioms N11Formalization.C450Source11GroupedC01.valid6
#print axioms N11Formalization.C450Source11GroupedC01.valid7
#print axioms N11Formalization.C450Source11GroupedC01.valid8
#print axioms N11Formalization.C450Source11GroupedC01.valid9
#print axioms N11Formalization.C450Source11GroupedC01.valid10
#print axioms N11Formalization.C450Source11GroupedC01.valid11
#print axioms N11Formalization.C450Source11GroupedC01.valid12
#print axioms N11Formalization.C450Source11GroupedC01.valid13
#print axioms N11Formalization.C450Source11GroupedC01.valid14
#print axioms N11Formalization.C450Source11GroupedC01.valid15
#print axioms N11Formalization.C450Source11GroupedC01.valid16
#print axioms N11Formalization.C450Source11GroupedC01.valid17
#print axioms N11Formalization.C450Source11GroupedC01.valid18
#print axioms N11Formalization.C450Source11GroupedC01.valid19
#print axioms N11Formalization.C450Source11GroupedC01.valid20
#print axioms N11Formalization.C450Source11GroupedC01.valid21
#print axioms N11Formalization.C450Source11GroupedC01.valid22
#print axioms N11Formalization.C450Source11GroupedC01.valid23
#print axioms N11Formalization.C450Source11GroupedC01.valid24
#print axioms N11Formalization.C450Source11GroupedC01.valid25
#print axioms N11Formalization.C450Source11GroupedC01.valid26
#print axioms N11Formalization.C450Source11GroupedC01.valid27
#print axioms N11Formalization.C450Source11GroupedC01.valid28
#print axioms N11Formalization.C450Source11GroupedC01.valid29
#print axioms N11Formalization.C450Source11GroupedC01.valid30
#print axioms N11Formalization.C450Source11GroupedC01.bound
#print axioms N11Formalization.C450Source11GroupedC01.endpoint_checks
