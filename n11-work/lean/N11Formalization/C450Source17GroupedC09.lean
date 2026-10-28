import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((6438980083:ℚ)/10000000000),((3366797713:ℚ)/5000000000),((-2766797713:ℚ)/6200000000),((-34832860581:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5600393253:ℚ)/10000000000),((6869846724300755122666820952108706130096494206810127040243:ℚ)/105857928125000000000000000000000000000000000000000000000000),((2439961662415323439331021939:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6677350931:ℚ)/10000000000),((6852779967:ℚ)/10000000000),((-5652779967:ℚ)/12875000000),((-36501456517:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4978761567:ℚ)/10000000000),((5845643252968754846346918781800470821764225053377470447843:ℚ)/92886739724218750000000000000000000000000000000000000000000),((2393851163902850122750124211:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((6796512571:ℚ)/10000000000),((1394389793:ℚ)/2000000000),((-1154389793:ℚ)/2622500000),((-12445195999:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2319905833:ℚ)/5000000000),((2325004808717258539107473903480075960213441444094106282023:ℚ)/36975624050000000000000000000000000000000000000000000000000),((2370706024419212319250263491:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((6915659491:ℚ)/10000000000),((3515763947:ℚ)/5000000000),((-2915763947:ℚ)/6675000000),((-38169616437:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2138101577:ℚ)/5000000000),((84243367469818189128347895251142575461183386690244312341:ℚ)/1359101524162292480468750000000000000000000000000000000000),((2347500770093177578134280531:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1743806919:ℚ)/2500000000),((7091103241:ℚ)/10000000000),((-5891103241:ℚ)/13468750000),((-9646648433:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2041550597:ℚ)/5000000000),((1675041137067039210522593423287260159227240940516476747431:ℚ)/27029371669580078125000000000000000000000000000000000000000),((437976667370941885931320033:ℚ)/2772480000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((1758698117:ℚ)/2500000000),((3575337549:ℚ)/5000000000),((-2975337549:ℚ)/6793750000),((-9750886819:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3880977807:ℚ)/10000000000),((361277339257126688381558798689750515975716962158362309743:ℚ)/5831016277546691894531250000000000000000000000000000000000),((145264704519868376258140739:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((1773588489:ℚ)/2500000000),((3605121779:ℚ)/5000000000),((-69886553:ℚ)/159375000),((-9855119423:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((733667553:ℚ)/2000000000),((3260845208523281029198096340286387560158319362508739229:ℚ)/52641181805419921875000000000000000000000000000000000000),((433608730195009567628867713:ℚ)/2772480000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3576956113:ℚ)/5000000000),((3634904353:ℚ)/5000000000),((-3034904353:ℚ)/6912500000),((-19918692791:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1721614347:ℚ)/5000000000),((11965087228241615407266751707468178075847837474557388103:ℚ)/193197798336791992187500000000000000000000000000000000000),((575227352808450225406449819:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((7213467359:ℚ)/10000000000),((1832342657:ℚ)/2500000000),((-1532342657:ℚ)/3485937500),((-40254271513:ℚ)/112500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3203017897:ℚ)/10000000000),((7202980937322116586207415944889114874656414208766560440973:ℚ)/116329121589660644531250000000000000000000000000000000000000),((2289223809545497725276446331:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7273019437:ℚ)/10000000000),((1477785881:ℚ)/2000000000),((-1237785881:ℚ)/2812500000),((-40671136059:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((147200297:ℚ)/500000000),((706217323756502887165485320449631796254601974556381203:ℚ)/11407842879882812500000000000000000000000000000000000000),((2277523075672492670278868019:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((916571067:ℚ)/1250000000),((1489697023:ℚ)/2000000000),((-1249697023:ℚ)/2836250000),((-5135997469:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((532140427:ℚ)/2000000000),((1283332839817139203533768214801262604952267431022025751633:ℚ)/20734455259375000000000000000000000000000000000000000000000),((106209712362810208090220617:ℚ)/693120000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7392114731:ℚ)/10000000000),((189189691:ℚ)/250000000),((-159189691:ℚ)/357500000),((-41504803117:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((293038731:ℚ)/1250000000),((3387136750046568290734400401607104470299733093918914789031:ℚ)/54073172553125000000000000000000000000000000000000000000000),((2254076161323090663270779811:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((1502239739:ℚ)/2000000000),((7686678783:ℚ)/10000000000),((-6486678783:ℚ)/14537500000),((-2822559391:ℚ)/7880000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((306035391:ℚ)/2000000000),((27829047537954125189522335057235730204593835451948426749:ℚ)/444578439950000000000000000000000000000000000000000000000),((89222742841648110170357571:ℚ)/591462400000000000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7630271879:ℚ)/10000000000),((396241453:ℚ)/500000000),((-336241453:ℚ)/738750000),((-43171903153:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((214536098656938034987819235626165955068449542032365598180151:ℚ)/3353644275000000000000000000000000000000000000000000000000000),((30650941:ℚ)/204800000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((7868387931:ℚ)/10000000000),((840101479:ℚ)/1000000000),((-720101479:ℚ)/1525000000),((-44838715517:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((9189203192698989048749597512067023883283089105268945153203:ℚ)/138316377600000000000000000000000000000000000000000000000000),((30650941:ℚ)/204800000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8344511273:ℚ)/10000000000),((2576157047:ℚ)/2500000000),((-2276157047:ℚ)/4050000000),((-48171578911:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3022629606351509589631406519210778169601817405727028930429:ℚ)/38400000000000000000000000000000000000000000000000000000000),((30650941:ℚ)/204800000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10247934703:ℚ)/10000000000),((564354603:ℚ)/400000000),((-516354603:ℚ)/800000000),((-20498514307:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((85252617277379827768642814121857264603898559886174665897:ℚ)/934425600000000000000000000000000000000000000000000000000),((30650941:ℚ)/204800000)⟩
theorem valid16 : Valid source17 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((2231:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC09
#check @N11Formalization.C450Source17GroupedC09.bound
#print axioms N11Formalization.C450Source17GroupedC09.valid0
#print axioms N11Formalization.C450Source17GroupedC09.valid1
#print axioms N11Formalization.C450Source17GroupedC09.valid2
#print axioms N11Formalization.C450Source17GroupedC09.valid3
#print axioms N11Formalization.C450Source17GroupedC09.valid4
#print axioms N11Formalization.C450Source17GroupedC09.valid5
#print axioms N11Formalization.C450Source17GroupedC09.valid6
#print axioms N11Formalization.C450Source17GroupedC09.valid7
#print axioms N11Formalization.C450Source17GroupedC09.valid8
#print axioms N11Formalization.C450Source17GroupedC09.valid9
#print axioms N11Formalization.C450Source17GroupedC09.valid10
#print axioms N11Formalization.C450Source17GroupedC09.valid11
#print axioms N11Formalization.C450Source17GroupedC09.valid12
#print axioms N11Formalization.C450Source17GroupedC09.valid13
#print axioms N11Formalization.C450Source17GroupedC09.valid14
#print axioms N11Formalization.C450Source17GroupedC09.valid15
#print axioms N11Formalization.C450Source17GroupedC09.valid16
#print axioms N11Formalization.C450Source17GroupedC09.bound
#print axioms N11Formalization.C450Source17GroupedC09.endpoint_checks
