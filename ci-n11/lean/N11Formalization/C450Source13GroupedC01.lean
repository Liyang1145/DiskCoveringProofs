import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1652652271:ℚ)/2500000000),((6798750003:ℚ)/10000000000),(-1:ℚ),((-1524652271:ℚ)/1685000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2579825369:ℚ)/5000000000),((722717273242034215890965153828457:ℚ)/14196125000000000000000000000000000),((20141220858731445007060667:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((6729394631:ℚ)/10000000000),((6917500003:ℚ)/10000000000),(-1:ℚ),((-18652183893:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((966684191:ℚ)/2000000000),((107706503900478088343652475444283349:ℚ)/2121800000000000000000000000000000000),((323356344687018715183875307:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3424089433:ℚ)/5000000000),((3488437501:ℚ)/5000000000),(-1:ℚ),((-352009937:ℚ)/385000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((448551589:ℚ)/1000000000),((2620272157809244763662176317417:ℚ)/52937500000000000000000000000000),((80974420792197262461795243:ℚ)/184832000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((3453785257:ℚ)/5000000000),((7036250003:ℚ)/10000000000),(-1:ℚ),((-9593355771:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((134431131:ℚ)/312500000),((13602722035917511395708396600120297:ℚ)/275100250000000000000000000000000000),((81111469027616960020749963:ℚ)/184832000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((348348093:ℚ)/500000000),((3532968751:ℚ)/5000000000),(-1:ℚ),((-322748093:ℚ)/351250000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((4110406643:ℚ)/10000000000),((12050063657232470325512098440741:ℚ)/246753125000000000000000000000000),((811790983828123580042163:ℚ)/1848320000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((6996657423:ℚ)/10000000000),((7095625003:ℚ)/10000000000),(-1:ℚ),((-19453972269:ℚ)/21170000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((200574661:ℚ)/500000000),((328154506237822186494599790691757417:ℚ)/6722533500000000000000000000000000000),((324990436871242010398998523:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7026352913:ℚ)/10000000000),((7125312503:ℚ)/10000000000),(-1:ℚ),((-19543058739:ℚ)/21265000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3910217489:ℚ)/10000000000),((330970509174711308923650233280292643:ℚ)/6783003375000000000000000000000000000),((325264465020376346537494203:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),(-1:ℚ),((-15:ℚ)/16),((1764012083:ℚ)/2500000000),((1785039063:ℚ)/2500000000),(-1:ℚ),((-4908036249:ℚ)/5328125000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((152255617:ℚ)/400000000),((34418088826795882036615528640853:ℚ)/709722900390625000000000000000000),((20337479411907585719569043:ℚ)/46208000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((1414179203:ℚ)/2000000000),((3577500001:ℚ)/5000000000),(-1:ℚ),((-1311779203:ℚ)/1424000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((3753454037:ℚ)/10000000000),((2761779860703527741811235857771:ℚ)/56960000000000000000000000000000),((13021466855246961843704883:ℚ)/29573120000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((22142949:ℚ)/31250000),((896230469:ℚ)/1250000000),(-1:ℚ),((-123257694:ℚ)/133796875),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((3699796767:ℚ)/10000000000),((6664906825775796720176520862578391:ℚ)/137484316875000000000000000000000000),((3180406917739145615587:ℚ)/7220000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((221893479:ℚ)/312500000),((3592343751:ℚ)/5000000000),(-1:ℚ),((-617680437:ℚ)/670468750),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((1822693359:ℚ)/5000000000),((3486105465618786034130925947965189:ℚ)/71924535156250000000000000000000000),((318174474195660413002667:ℚ)/722000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7115438959:ℚ)/10000000000),((1799882813:ℚ)/2500000000),(-1:ℚ),((-6603438959:ℚ)/7167500000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((718037921:ℚ)/2000000000),((397269739531299299622386392612973:ℚ)/8197828125000000000000000000000000),((325947650980790345773295547:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((7130286573:ℚ)/10000000000),((7214375003:ℚ)/10000000000),(-1:ℚ),((-19854859719:ℚ)/21550000000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3534168489:ℚ)/10000000000),((7031615940797432322728833928337101:ℚ)/145125781250000000000000000000000000),((326084636599155038201674323:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((431:ℚ)/640),((17259:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7145134169:ℚ)/10000000000),((3610898439:ℚ)/5000000000),(-1:ℚ),((-6633134169:ℚ)/7191250000),((1943277549:ℚ)/2000000000),((9719670101:ℚ)/10000000000),((1193656329:ℚ)/5000000000),((1738641743:ℚ)/5000000000),((4996160872719514603686096102155783:ℚ)/103428153125000000000000000000000000),((326152214718883997176008107:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((17259:ℚ)/25600) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((17259:ℚ)/25600),((8639:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7152557961:ℚ)/10000000000),((112956543:ℚ)/156250000),(-1:ℚ),((-19921673883:ℚ)/21597500000),((4856560387:ℚ)/5000000000),((38865551:ℚ)/40000000),((9604357:ℚ)/40000000),((3448503671:ℚ)/10000000000),((345558358100407254413126552373371:ℚ)/7154171875000000000000000000000000),((17169510747004077030269033:ℚ)/38912000000000000000000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((17259:ℚ)/25600) ((8639:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8639:ℚ)/12800),((17297:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7159981749:ℚ)/10000000000),((7236640627:ℚ)/10000000000),(-1:ℚ),((-19943945247:ℚ)/21621250000),((9709869133:ℚ)/10000000000),((9713120779:ℚ)/10000000000),((2414724647:ℚ)/10000000000),((3419491413:ℚ)/10000000000),((225781407255485905463805932823341659:ℚ)/4674784515625000000000000000000000000),((326289192727744358298304387:ℚ)/739328000000000000000000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell ((8639:ℚ)/12800) ((17297:ℚ)/25600) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((17297:ℚ)/25600),((4329:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1791851383:ℚ)/2500000000),((3622031251:ℚ)/5000000000),(-1:ℚ),((-1663851383:ℚ)/1803750000),((2426658193:ℚ)/2500000000),((4854934569:ℚ)/5000000000),((2428221417:ℚ)/10000000000),((1695120371:ℚ)/5000000000),((392811306610321184660244964336819:ℚ)/8133785156250000000000000000000000),((20397355019603652943709643:ℚ)/46208000000000000000000000)⟩
theorem valid16 : Valid source13 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source13 nn0 nn1 Qcell ((17297:ℚ)/25600) ((4329:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4329:ℚ)/6400),((3467:ℚ)/5120),(-1:ℚ),((-15:ℚ)/16),((28026677:ℚ)/39062500),((7251484377:ℚ)/10000000000),(-1:ℚ),((-1249280496:ℚ)/1354296875),((242585291:ℚ)/250000000),((9706632777:ℚ)/10000000000),((2441582049:ℚ)/10000000000),((420093177:ℚ)/1250000000),((136042659187991762500334732509067483:ℚ)/2817208359375000000000000000000000000),((622608503247403070431:ℚ)/1410156250000000000000)⟩
theorem valid17 : Valid source13 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source13 nn0 nn1 Qcell ((4329:ℚ)/6400) ((3467:ℚ)/5120) :=
  cell_of_packet source13 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((3467:ℚ)/5120),((8677:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7182253087:ℚ)/10000000000),((1814726563:ℚ)/2500000000),(-1:ℚ),((-20010759261:ℚ)/21692500000),((9700205687:ℚ)/10000000000),((1940682329:ℚ)/2000000000),((306851119:ℚ)/1250000000),((666199787:ℚ)/2000000000),((113608382727134063150279733497553747:ℚ)/2352822781250000000000000000000000000),((326494652638740993892322203:ℚ)/739328000000000000000000000)⟩
theorem valid18 : Valid source13 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source13 nn0 nn1 Qcell ((3467:ℚ)/5120) ((8677:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((8677:ℚ)/12800),((17373:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((3594838429:ℚ)/5000000000),((7266328127:ℚ)/10000000000),(-1:ℚ),((-3338838429:ℚ)/3619375000),((9697014863:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2467904459:ℚ)/10000000000),((3300994499:ℚ)/10000000000),((3162448789954791871628986101870363:ℚ)/65499376953125000000000000000000000),((81640784344509028665402867:ℚ)/184832000000000000000000000)⟩
theorem valid19 : Valid source13 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source13 nn0 nn1 Qcell ((8677:ℚ)/12800) ((17373:ℚ)/25600) :=
  cell_of_packet source13 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((17373:ℚ)/25600),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((11515361:ℚ)/16000000),((3636875001:ℚ)/5000000000),(-1:ℚ),((-32088483:ℚ)/34784000),((9693839119:ℚ)/10000000000),((2424253717:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((3270724999:ℚ)/10000000000),((36508225199683117733912392964957:ℚ)/756204160000000000000000000000000),((4180884750956305380871:ℚ)/9463398400000000000000)⟩
theorem valid20 : Valid source13 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source13 nn0 nn1 Qcell ((17373:ℚ)/25600) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((7204524387:ℚ)/10000000000),((7288593753:ℚ)/10000000000),(-1:ℚ),((-6692524387:ℚ)/7262500000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((3240183003:ℚ)/10000000000),((5471487619638973820741982089165003:ℚ)/113022656250000000000000000000000000),((326769507713493597827951603:ℚ)/739328000000000000000000000)⟩
theorem valid21 : Valid source13 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source13 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((72193719:ℚ)/100000000),((7303437503:ℚ)/10000000000),(-1:ℚ),((-201221157:ℚ)/218350000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((158912499:ℚ)/500000000),((5769180168193884241850923370947:ℚ)/119191806250000000000000000000000),((32690647055013312440907:ℚ)/73932800000000000000000)⟩
theorem valid22 : Valid source13 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7234219397:ℚ)/10000000000),((7318281253:ℚ)/10000000000),(-1:ℚ),((-20166658191:ℚ)/21882500000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((311512847:ℚ)/1000000000),((11586706145673058247997856464761703:ℚ)/239421903125000000000000000000000000),((327043429591318205601395683:ℚ)/739328000000000000000000000)⟩
theorem valid23 : Valid source13 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source13 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7249066877:ℚ)/10000000000),((3666562501:ℚ)/5000000000),(-1:ℚ),((-6737066877:ℚ)/7310000000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((762686159:ℚ)/2500000000),((6463978558972616849640655679535401:ℚ)/133590250000000000000000000000000000),((327180384827834755894159923:ℚ)/739328000000000000000000000)⟩
theorem valid24 : Valid source13 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source13 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3631957171:ℚ)/5000000000),((459248047:ℚ)/625000000),(-1:ℚ),((-10127871513:ℚ)/10988750000),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((2985016719:ℚ)/10000000000),((58418630396252819210018281800504587:ℚ)/1207526265625000000000000000000000000),((81829334069537007981925267:ℚ)/184832000000000000000000000)⟩
theorem valid25 : Valid source13 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((727876179:ℚ)/1000000000),((3681406251:ℚ)/5000000000),(-1:ℚ),((-2030028537:ℚ)/2202500000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((1458926913:ℚ)/5000000000),((586620007304484030090145763586693:ℚ)/12127515625000000000000000000000000),((3274542839331690763526867:ℚ)/7393280000000000000000000)⟩
theorem valid26 : Valid source13 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source13 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source13 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((3646804611:ℚ)/5000000000),((7392500003:ℚ)/10000000000),(-1:ℚ),((-10172413833:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2849154401:ℚ)/10000000000),((531113039676280442507826207232091:ℚ)/10921750000000000000000000000000000),((81932508797534131971442227:ℚ)/184832000000000000000000000)⟩
theorem valid27 : Valid source13 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7323304039:ℚ)/10000000000),((3711093751:ℚ)/5000000000),(-1:ℚ),((-6811304039:ℚ)/7405000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((2706675067:ℚ)/10000000000),((6663994526118462331550187919967281:ℚ)/137085062500000000000000000000000000),((328003911513726199945443627:ℚ)/739328000000000000000000000)⟩
theorem valid28 : Valid source13 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7352998793:ℚ)/10000000000),((3725937501:ℚ)/5000000000),(-1:ℚ),((-20522996379:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((639117987:ℚ)/2500000000),((30234715099088585267114996607769543:ℚ)/622170125000000000000000000000000000),((328277772665067429618159563:ℚ)/739328000000000000000000000)⟩
theorem valid29 : Valid source13 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),(-1:ℚ),((-15:ℚ)/16),((3691346743:ℚ)/5000000000),((3755625001:ℚ)/5000000000),(-1:ℚ),((-1145115581:ℚ)/1250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((149818303:ℚ)/625000000),((23972211619030059270610018452109:ℚ)/488281250000000000000000000000000),((82207308352662827853573963:ℚ)/184832000000000000000000000)⟩
theorem valid30 : Valid source13 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((7442082689:ℚ)/10000000000),((7630000003:ℚ)/10000000000),(-1:ℚ),((-20790248067:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((204210447:ℚ)/1000000000),((131015346741583592356985449767989699:ℚ)/2617472000000000000000000000000000000),((329651572301418995276680027:ℚ)/739328000000000000000000000)⟩
theorem valid31 : Valid source13 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),(-1:ℚ),((-15:ℚ)/16),((3780430193:ℚ)/5000000000),((4052500001:ℚ)/5000000000),(-1:ℚ),((-10573290579:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((101532021:ℚ)/1000000000),((123370951324827793779731336030617253:ℚ)/2232600000000000000000000000000000000),((82409055951498570353434363:ℚ)/184832000000000000000000000)⟩
theorem valid32 : Valid source13 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet32 valid32
def packet33 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((8035962547:ℚ)/10000000000),((8580000003:ℚ)/10000000000),(-1:ℚ),((-7523962547:ℚ)/8640000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((20356638030056298000351749462520521:ℚ)/373248000000000000000000000000000000),((114138197:ℚ)/256000000)⟩
theorem valid33 : Valid source13 packet33 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf33 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet33 valid33
def packet34 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((8511052723:ℚ)/10000000000),((5240000001:ℚ)/5000000000),(-1:ℚ),((-23997158169:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1034653049079831565179648857856438593:ℚ)/15360000000000000000000000000000000000),((114138197:ℚ)/256000000)⟩
theorem valid34 : Valid source13 packet34 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf34 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet34 valid34
def packet35 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((10411327741:ℚ)/10000000000),((14280000003:ℚ)/10000000000),(-1:ℚ),((-9899327741:ℚ)/14720000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8332045049249722831802191:ℚ)/108339200000000000000000000),((114138197:ℚ)/256000000)⟩
theorem valid35 : Valid source13 packet35 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf35 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet35 valid35
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source13 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source13 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source13 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source13 nn0 nn1 Qcell ((17297:ℚ)/25600) ((3467:ℚ)/5120) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source13 nn0 nn1 Qcell ((8639:ℚ)/12800) ((3467:ℚ)/5120) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((3467:ℚ)/5120) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((3467:ℚ)/5120) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((3467:ℚ)/5120) :=
  cell_join node0_9 node9_18
private theorem node18_20 :
    CellBound source13 nn0 nn1 Qcell ((3467:ℚ)/5120) ((17373:ℚ)/25600) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound source13 nn0 nn1 Qcell ((17373:ℚ)/25600) ((1743:ℚ)/2560) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound source13 nn0 nn1 Qcell ((3467:ℚ)/5120) ((1743:ℚ)/2560) :=
  cell_join node18_20 node20_22
private theorem node22_24 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((8753:ℚ)/12800) :=
  cell_join leaf22 leaf23
private theorem node25_27 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_join leaf25 leaf26
private theorem node24_27 :
    CellBound source13 nn0 nn1 Qcell ((8753:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_join leaf24 node25_27
private theorem node22_27 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((881:ℚ)/1280) :=
  cell_join node22_24 node24_27
private theorem node18_27 :
    CellBound source13 nn0 nn1 Qcell ((3467:ℚ)/5120) ((881:ℚ)/1280) :=
  cell_join node18_22 node22_27
private theorem node27_29 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf27 leaf28
private theorem node29_31 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf29 leaf30
private theorem node27_31 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((45:ℚ)/64) :=
  cell_join node27_29 node29_31
private theorem node31_33 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf31 leaf32
private theorem node34_36 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf34 leaf35
private theorem node33_36 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf33 node34_36
private theorem node31_36 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node31_33 node33_36
private theorem node27_36 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node27_31 node31_36
private theorem node18_36 :
    CellBound source13 nn0 nn1 Qcell ((3467:ℚ)/5120) ((69:ℚ)/50) :=
  cell_join node18_27 node27_36
private theorem node0_36 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_18 node18_36
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_36
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32,packet33,packet34,packet35]
theorem packet_count : packets.length = 36 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC01
#check @N11Formalization.C450Source13GroupedC01.bound
#print axioms N11Formalization.C450Source13GroupedC01.valid0
#print axioms N11Formalization.C450Source13GroupedC01.valid1
#print axioms N11Formalization.C450Source13GroupedC01.valid2
#print axioms N11Formalization.C450Source13GroupedC01.valid3
#print axioms N11Formalization.C450Source13GroupedC01.valid4
#print axioms N11Formalization.C450Source13GroupedC01.valid5
#print axioms N11Formalization.C450Source13GroupedC01.valid6
#print axioms N11Formalization.C450Source13GroupedC01.valid7
#print axioms N11Formalization.C450Source13GroupedC01.valid8
#print axioms N11Formalization.C450Source13GroupedC01.valid9
#print axioms N11Formalization.C450Source13GroupedC01.valid10
#print axioms N11Formalization.C450Source13GroupedC01.valid11
#print axioms N11Formalization.C450Source13GroupedC01.valid12
#print axioms N11Formalization.C450Source13GroupedC01.valid13
#print axioms N11Formalization.C450Source13GroupedC01.valid14
#print axioms N11Formalization.C450Source13GroupedC01.valid15
#print axioms N11Formalization.C450Source13GroupedC01.valid16
#print axioms N11Formalization.C450Source13GroupedC01.valid17
#print axioms N11Formalization.C450Source13GroupedC01.valid18
#print axioms N11Formalization.C450Source13GroupedC01.valid19
#print axioms N11Formalization.C450Source13GroupedC01.valid20
#print axioms N11Formalization.C450Source13GroupedC01.valid21
#print axioms N11Formalization.C450Source13GroupedC01.valid22
#print axioms N11Formalization.C450Source13GroupedC01.valid23
#print axioms N11Formalization.C450Source13GroupedC01.valid24
#print axioms N11Formalization.C450Source13GroupedC01.valid25
#print axioms N11Formalization.C450Source13GroupedC01.valid26
#print axioms N11Formalization.C450Source13GroupedC01.valid27
#print axioms N11Formalization.C450Source13GroupedC01.valid28
#print axioms N11Formalization.C450Source13GroupedC01.valid29
#print axioms N11Formalization.C450Source13GroupedC01.valid30
#print axioms N11Formalization.C450Source13GroupedC01.valid31
#print axioms N11Formalization.C450Source13GroupedC01.valid32
#print axioms N11Formalization.C450Source13GroupedC01.valid33
#print axioms N11Formalization.C450Source13GroupedC01.valid34
#print axioms N11Formalization.C450Source13GroupedC01.valid35
#print axioms N11Formalization.C450Source13GroupedC01.bound
#print axioms N11Formalization.C450Source13GroupedC01.endpoint_checks
