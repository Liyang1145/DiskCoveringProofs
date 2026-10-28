import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((1493910907:ℚ)/2500000000),((6496420391:ℚ)/10000000000),((1605910907:ℚ)/2670000000),((76580624301:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6660492573:ℚ)/10000000000),((-36612692342802935473390430425673:ℚ)/4758540750000000000000000000000000),((-137744189537034958682389727:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6450953827:ℚ)/10000000000),((3367021721:ℚ)/5000000000),((6898953827:ℚ)/11060000000),((39597238931:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2785332349:ℚ)/5000000000),((-255062250894733385212547511034746063389039791991299057:ℚ)/25366856550000000000000000000000000000000000000000000000),((-2211394655684729195961541167:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((3344296463:ℚ)/5000000000),((856606481:ℚ)/1250000000),((3568296463:ℚ)/5625000000),((10062671291:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4947698471:ℚ)/10000000000),((-4129931566915485171163898234012294753069357156689933:ℚ)/370788574218750000000000000000000000000000000000000000),((-553822584949088302792451287:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((1701852237:ℚ)/2500000000),((6971658313:ℚ)/10000000000),((1813852237:ℚ)/2860000000),((81808241443:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((9215341:ℚ)/20000000),((-148934202257283227232815616970505961994282852963111:ℚ)/13291850000000000000000000000000000000000000000000000),((-415739278494067735221006061:ℚ)/2772480000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((865777847:ℚ)/1250000000),((7031060847:ℚ)/10000000000),((921777847:ℚ)/1441875000),((82461669317:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4242563533:ℚ)/10000000000),((-164547442239600870374426161135885805170381143248597:ℚ)/14051546222305297851562500000000000000000000000000000),((-34676363722338717683535207:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6985628901:ℚ)/10000000000),((7090462931:ℚ)/10000000000),((7433628901:ℚ)/11630000000),((27705030747:ℚ)/38450000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((161939789:ℚ)/400000000),((-4614528578373671413186919228708493783243405592785053:ℚ)/393259436750000000000000000000000000000000000000000000),((-18451265935873473211177429:ℚ)/122880000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((7045034517:ℚ)/10000000000),((55858317:ℚ)/78125000),((7493034517:ℚ)/11725000000),((654441487:ℚ)/908593750),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3845209823:ℚ)/10000000000),((-12690055384140212542576902209236707029856841148687969:ℚ)/1079398461914062500000000000000000000000000000000000000),((-6663971157064040296549457341:ℚ)/44359680000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1776109909:ℚ)/2500000000),((56322389:ℚ)/78125000),((1888109909:ℚ)/2955000000),((94220897:ℚ)/130859375),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3631157369:ℚ)/10000000000),((-52761738664721974877303977040485588854962739236557:ℚ)/4479710742187500000000000000000000000000000000000000),((-138896964530546003248297663:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((7163844271:ℚ)/10000000000),((726866659:ℚ)/1000000000),((7611844271:ℚ)/11915000000),((8507533249:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3404302717:ℚ)/10000000000),((-374192638172871009995436635275681425797703160337611189:ℚ)/31716365360156250000000000000000000000000000000000000000),((-2223385474753532807860152343:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7223248433:ℚ)/10000000000),((366403349:ℚ)/500000000),((7671248433:ℚ)/12010000000),((4286436839:ℚ)/5957500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((31618871:ℚ)/100000000),((-7996505543770657561249533998836685270801751315184841:ℚ)/676688906640625000000000000000000000000000000000000000),((-2224425845854075673685033047:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((7282652133:ℚ)/10000000000),((738746697:ℚ)/1000000000),((7730652133:ℚ)/12105000000),((8638213667:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2900006081:ℚ)/10000000000),((-4859360677461600548423297873902505188649129096604463:ℚ)/410592142968750000000000000000000000000000000000000000),((-6676417637500194875654318941:ℚ)/44359680000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((3671027691:ℚ)/5000000000),((1861716643:ℚ)/2500000000),((3895027691:ℚ)/6100000000),((21758883073:ℚ)/30262500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2612807929:ℚ)/10000000000),((-16813360734948790661207852559496342845003636287213483:ℚ)/1418631250000000000000000000000000000000000000000000000),((-1669894181054421910859833789:ℚ)/11089920000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7401458191:ℚ)/10000000000),((3782832321:ℚ)/5000000000),((7849458191:ℚ)/12390000000),((44171155531:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1145392173:ℚ)/5000000000),((-1261006715584676447607740874464261457871072297507709:ℚ)/110070307812500000000000000000000000000000000000000000),((-2227584932623991812898434263:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((7520262529:ℚ)/10000000000),((7684461259:ℚ)/10000000000),((7968262529:ℚ)/12580000000),((89649073849:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1449839319:ℚ)/10000000000),((-139645253727044046972679263633479561838641269833873:ℚ)/12151278759765625000000000000000000000000000000000000),((-6176516995820162055352863:ℚ)/40960000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((305562609:ℚ)/400000000),((7922050391:ℚ)/10000000000),((323482609:ℚ)/518400000),((92262554301:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-346913452521679358210316810435681574628322462619:ℚ)/32248627200000000000000000000000000000000000000000),((-154513269:ℚ)/1024000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((3938332989:ℚ)/5000000000),((9822610967:ℚ)/10000000000),((4162332989:ℚ)/8000000000),((12574302293:ℚ)/14400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-1875235716890978739235152738811290409332522272226919:ℚ)/600000000000000000000000000000000000000000000000000000),((-154513269:ℚ)/1024000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9777299633:ℚ)/10000000000),((3405817229:ℚ)/2500000000),((3408433211:ℚ)/7360000000),((38743989519:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((31299765794857031309219:ℚ)/13542400000000000000000000),((-154513269:ℚ)/1024000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC27
#check @N11Formalization.C450NinthGroupedC27.bound
#print axioms N11Formalization.C450NinthGroupedC27.valid0
#print axioms N11Formalization.C450NinthGroupedC27.valid1
#print axioms N11Formalization.C450NinthGroupedC27.valid2
#print axioms N11Formalization.C450NinthGroupedC27.valid3
#print axioms N11Formalization.C450NinthGroupedC27.valid4
#print axioms N11Formalization.C450NinthGroupedC27.valid5
#print axioms N11Formalization.C450NinthGroupedC27.valid6
#print axioms N11Formalization.C450NinthGroupedC27.valid7
#print axioms N11Formalization.C450NinthGroupedC27.valid8
#print axioms N11Formalization.C450NinthGroupedC27.valid9
#print axioms N11Formalization.C450NinthGroupedC27.valid10
#print axioms N11Formalization.C450NinthGroupedC27.valid11
#print axioms N11Formalization.C450NinthGroupedC27.valid12
#print axioms N11Formalization.C450NinthGroupedC27.valid13
#print axioms N11Formalization.C450NinthGroupedC27.valid14
#print axioms N11Formalization.C450NinthGroupedC27.valid15
#print axioms N11Formalization.C450NinthGroupedC27.valid16
#print axioms N11Formalization.C450NinthGroupedC27.bound
#print axioms N11Formalization.C450NinthGroupedC27.endpoint_checks
