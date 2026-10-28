import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((79838867:ℚ)/125000000),((6677500003:ℚ)/10000000000),(-1:ℚ),((-229916601:ℚ)/257500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2863793171:ℚ)/5000000000),((443728287538337666499853252917:ℚ)/33153125000000000000000000000000),((11337522555895696640539:ℚ)/57760000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((6624623773:ℚ)/10000000000),((3398125001:ℚ)/5000000000),(-1:ℚ),((-19105871319:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((256107533:ℚ)/500000000),((1401181834646927014508601919131129:ℚ)/110040100000000000000000000000000000),((72663822579903656648088379:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((1685845147:ℚ)/2500000000),((3457500001:ℚ)/5000000000),(-1:ℚ),((-1621845147:ℚ)/1780000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((239683643:ℚ)/500000000),((10062246135036793866120786794523:ℚ)/792100000000000000000000000000000),((4548753049181965202516459:ℚ)/23104000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((171553429:ℚ)/250000000),((3487187501:ℚ)/5000000000),(-1:ℚ),((-495460287:ℚ)/538750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1110744071:ℚ)/2500000000),((10795826294444100707867982529703:ℚ)/870754687500000000000000000000000),((45519562019278110615691:ℚ)/231040000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((6921515359:ℚ)/10000000000),((3516875001:ℚ)/5000000000),(-1:ℚ),((-19996546077:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2128792749:ℚ)/5000000000),((2927514936361643913396592594244937:ℚ)/236313800000000000000000000000000000),((72889206300633901927242531:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3490446751:ℚ)/5000000000),((7063437503:ℚ)/10000000000),(-1:ℚ),((-10087340253:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((2032142313:ℚ)/5000000000),((49736897745031941065495762896151:ℚ)/4063357031250000000000000000000000),((18228671089181213818847651:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3505291277:ℚ)/5000000000),((3546562501:ℚ)/5000000000),(-1:ℚ),((-3377291277:ℚ)/3655000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3964307053:ℚ)/10000000000),((40866934800662105779713465804917:ℚ)/3339756250000000000000000000000000),((18235896595491405424703579:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((7040271591:ℚ)/10000000000),((3561406251:ℚ)/5000000000),(-1:ℚ),((-20352814773:ℚ)/22025000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((30895059:ℚ)/80000000),((1483525904549295936401128431800021:ℚ)/121275156250000000000000000000000000),((72972473691778202846474931:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((883745077:ℚ)/1250000000),((7152500003:ℚ)/10000000000),(-1:ℚ),((-2555235231:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3756809969:ℚ)/10000000000),((417382178123841525496014193139:ℚ)/34130468750000000000000000000000),((1140646035716105386728779:ℚ)/5776000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7099649627:ℚ)/10000000000),((895917969:ℚ)/1250000000),(-1:ℚ),((-20530948881:ℚ)/22167500000),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((3648860639:ℚ)/10000000000),((1493499013256953166899516695531003:ℚ)/122849514062500000000000000000000000),((73014019087107105574511979:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((444655883:ℚ)/625000000),((3591093751:ℚ)/5000000000),(-1:ℚ),((-428655883:ℚ)/462812500),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3593726227:ℚ)/10000000000),((124975870338790600887615835407431:ℚ)/10281379687500000000000000000000000),((285267353540955390606539:ℚ)/1444000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((57034709:ℚ)/80000000),((1799257813:ℚ)/2500000000),(-1:ℚ),((-164960127:ℚ)/178100000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((707554109:ℚ)/2000000000),((963798865626824987581842248643:ℚ)/79299025000000000000000000000000),((4674743183793929576971:ℚ)/23658496000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((89302289:ℚ)/125000000),((3605937501:ℚ)/5000000000),(-1:ℚ),((-258306867:ℚ)/278875000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((3480953917:ℚ)/10000000000),((118138660880981371152690829009:ℚ)/9721408203125000000000000000000),((11415199735587219039171:ℚ)/57760000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2231:ℚ)/3200),((8943:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7159027611:ℚ)/10000000000),((7226718753:ℚ)/10000000000),(-1:ℚ),((-6903027611:ℚ)/7452500000),((961640533:ℚ)/1000000000),((9622019977:ℚ)/10000000000),((555749933:ℚ)/2000000000),((3423233421:ℚ)/10000000000),((766882746162980649315135332439:ℚ)/63113359375000000000000000000000),((73071690690749669633236971:ℚ)/369664000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((8943:ℚ)/12800) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8943:ℚ)/12800),((4481:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7173872099:ℚ)/10000000000),((7241562503:ℚ)/10000000000),(-1:ℚ),((-20753616297:ℚ)/22405000000),((1922169193:ℚ)/2000000000),((1923281067:ℚ)/2000000000),((349868089:ℚ)/1250000000),((3364562471:ℚ)/10000000000),((1829633589396786104397602675648957:ℚ)/150595207500000000000000000000000000),((73086099393457012391227451:ℚ)/369664000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((8943:ℚ)/12800) ((4481:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4481:ℚ)/6400),((8981:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((898589573:ℚ)/1250000000),((1814101563:ℚ)/2500000000),(-1:ℚ),((-2599768719:ℚ)/2806562500),((4802670763:ℚ)/5000000000),((961084597:ℚ)/1000000000),((563760281:ℚ)/2000000000),((3304890383:ℚ)/10000000000),((382743829398680981601294635629381:ℚ)/31507172265625000000000000000000000),((1142195381498163452875179:ℚ)/5776000000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((8981:ℚ)/12800) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8981:ℚ)/12800),((45:ℚ)/64),(-1:ℚ),((-15:ℚ)/16),((3601780533:ℚ)/5000000000),((3635625001:ℚ)/5000000000),(-1:ℚ),((-3473780533:ℚ)/3750000000),((599993229:ℚ)/625000000),((9605341531:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1622080923:ℚ)/5000000000),((1779247469497047411537402589799:ℚ)/146484375000000000000000000000000),((18278726440052243007620939:ℚ)/92416000000000000000000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((8981:ℚ)/12800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((45:ℚ)/64),((9019:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1443681109:ℚ)/2000000000),((910761719:ℚ)/1250000000),(-1:ℚ),((-4177443327:ℚ)/4509500000),((1918899207:ℚ)/2000000000),((9599891669:ℚ)/10000000000),((357191541:ℚ)/1250000000),((636463263:ℚ)/2000000000),((24697250283168673037440919476683:ℚ)/2033559025000000000000000000000000),((2925172137013936540363531:ℚ)/14786560000000000000000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((9019:ℚ)/12800) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((9019:ℚ)/12800),((4519:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((361662501:ℚ)/500000000),((3650468751:ℚ)/5000000000),(-1:ℚ),((-1046587503:ℚ)/1129750000),((9589154297:ℚ)/10000000000),((239862401:ℚ)/250000000),((575284399:ℚ)/2000000000),((1559643643:ℚ)/5000000000),((7749501511630308637487603970551:ℚ)/638167531250000000000000000000000),((182859243528559492716651:ℚ)/924160000000000000000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((9019:ℚ)/12800) ((4519:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7248094493:ℚ)/10000000000),((7330625003:ℚ)/10000000000),(-1:ℚ),((-20976283479:ℚ)/22690000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((305500143:ℚ)/1000000000),((157129414216513235543881236968219:ℚ)/12870902500000000000000000000000000),((73174272793286402756067899:ℚ)/369664000000000000000000000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7277783429:ℚ)/10000000000),((3680156251:ℚ)/5000000000),(-1:ℚ),((-7021783429:ℚ)/7595000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((2922325591:ℚ)/10000000000),((352012048654129194204542276432871:ℚ)/28842012500000000000000000000000000),((73203042368323149753355691:ℚ)/369664000000000000000000000)⟩
theorem valid20 : Valid seventh packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((7307472353:ℚ)/10000000000),((7390000003:ℚ)/10000000000),(-1:ℚ),((-21154417059:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1391760857:ℚ)/5000000000),((290339938343607502440800767589137:ℚ)/23795200000000000000000000000000000),((73231797228837952871671459:ℚ)/369664000000000000000000000)⟩
theorem valid21 : Valid seventh packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3668580633:ℚ)/5000000000),((3724687501:ℚ)/5000000000),(-1:ℚ),((-3540580633:ℚ)/3845000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((659405469:ℚ)/2500000000),((854271161773958311067627522171:ℚ)/69300117187500000000000000000000),((18323226879591172878927539:ℚ)/92416000000000000000000000)⟩
theorem valid22 : Valid seventh packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((462283691:ℚ)/625000000),((7508750003:ℚ)/10000000000),(-1:ℚ),((-1338851073:ℚ)/1453750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2319115623:ℚ)/10000000000),((26035881897619746442041749905923:ℚ)/2113389062500000000000000000000000),((286524779901184382517131:ℚ)/1444000000000000000000000)⟩
theorem valid23 : Valid seventh packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((1164987:ℚ)/1562500),((3813750001:ℚ)/5000000000),(-1:ℚ),((-1124987:ℚ)/1231250),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1950308873:ℚ)/10000000000),((4569145264587060388558409947:ℚ)/363834375000000000000000000000),((1793029204997611519:ℚ)/9025000000000000000)⟩
theorem valid24 : Valid seventh packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(-1:ℚ),((-15:ℚ)/16),((1893668039:ℚ)/2500000000),((3932500001:ℚ)/5000000000),(-1:ℚ),((-5489004117:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((816635019:ℚ)/10000000000),((725663838737069305010803711604029:ℚ)/55815000000000000000000000000000000),((4589223348818525549005171:ℚ)/23104000000000000000000000)⟩
theorem valid25 : Valid seventh packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((244130699:ℚ)/312500000),((8340000003:ℚ)/10000000000),(-1:ℚ),((-78710233:ℚ)/90000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((55768294848249567830182341497:ℚ)/4050000000000000000000000000000),((25423949:ℚ)/128000000)⟩
theorem valid26 : Valid seventh packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((1657440199:ℚ)/2000000000),((5120000001:ℚ)/5000000000),(-1:ℚ),((-4818720597:ℚ)/6400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1049594375590445165939639176755889:ℚ)/61440000000000000000000000000000000),((25423949:ℚ)/128000000)⟩
theorem valid27 : Valid seventh packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((10187257807:ℚ)/10000000000),((14040000003:ℚ)/10000000000),(-1:ℚ),((-9931257807:ℚ)/14720000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((211870600632633115835663:ℚ)/10833920000000000000000000),((25423949:ℚ)/128000000)⟩
theorem valid28 : Valid seventh packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet28 valid28
private theorem node1_3 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((881:ℚ)/1280) ((8867:ℚ)/12800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((8867:ℚ)/12800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((8867:ℚ)/12800) ((1781:ℚ)/2560) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((1781:ℚ)/2560) ((8943:ℚ)/12800) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound seventh nn0 nn1 Qcell ((8867:ℚ)/12800) ((8943:ℚ)/12800) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((8943:ℚ)/12800) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((8943:ℚ)/12800) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound seventh nn0 nn1 Qcell ((8943:ℚ)/12800) ((45:ℚ)/64) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4557:ℚ)/6400) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound seventh nn0 nn1 Qcell ((8943:ℚ)/12800) ((4557:ℚ)/6400) :=
  cell_join node14_17 node17_21
private theorem node21_23 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join node21_23 node23_25
private theorem node25_27 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf25 leaf26
private theorem node27_29 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf27 leaf28
private theorem node25_29 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node25_27 node27_29
private theorem node21_29 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node21_25 node25_29
private theorem node14_29 :
    CellBound seventh nn0 nn1 Qcell ((8943:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node14_21 node21_29
private theorem node0_29 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_29
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_29
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28]
theorem packet_count : packets.length = 29 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC01
#check @N11Formalization.C450SeventhGroupedC01.bound
#print axioms N11Formalization.C450SeventhGroupedC01.valid0
#print axioms N11Formalization.C450SeventhGroupedC01.valid1
#print axioms N11Formalization.C450SeventhGroupedC01.valid2
#print axioms N11Formalization.C450SeventhGroupedC01.valid3
#print axioms N11Formalization.C450SeventhGroupedC01.valid4
#print axioms N11Formalization.C450SeventhGroupedC01.valid5
#print axioms N11Formalization.C450SeventhGroupedC01.valid6
#print axioms N11Formalization.C450SeventhGroupedC01.valid7
#print axioms N11Formalization.C450SeventhGroupedC01.valid8
#print axioms N11Formalization.C450SeventhGroupedC01.valid9
#print axioms N11Formalization.C450SeventhGroupedC01.valid10
#print axioms N11Formalization.C450SeventhGroupedC01.valid11
#print axioms N11Formalization.C450SeventhGroupedC01.valid12
#print axioms N11Formalization.C450SeventhGroupedC01.valid13
#print axioms N11Formalization.C450SeventhGroupedC01.valid14
#print axioms N11Formalization.C450SeventhGroupedC01.valid15
#print axioms N11Formalization.C450SeventhGroupedC01.valid16
#print axioms N11Formalization.C450SeventhGroupedC01.valid17
#print axioms N11Formalization.C450SeventhGroupedC01.valid18
#print axioms N11Formalization.C450SeventhGroupedC01.valid19
#print axioms N11Formalization.C450SeventhGroupedC01.valid20
#print axioms N11Formalization.C450SeventhGroupedC01.valid21
#print axioms N11Formalization.C450SeventhGroupedC01.valid22
#print axioms N11Formalization.C450SeventhGroupedC01.valid23
#print axioms N11Formalization.C450SeventhGroupedC01.valid24
#print axioms N11Formalization.C450SeventhGroupedC01.valid25
#print axioms N11Formalization.C450SeventhGroupedC01.valid26
#print axioms N11Formalization.C450SeventhGroupedC01.valid27
#print axioms N11Formalization.C450SeventhGroupedC01.valid28
#print axioms N11Formalization.C450SeventhGroupedC01.bound
#print axioms N11Formalization.C450SeventhGroupedC01.endpoint_checks
