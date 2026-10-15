import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6595967663:ℚ)/10000000000),((6803861113:ℚ)/10000000000),((-4643861113:ℚ)/12400000000),((-28251773641:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5198564823:ℚ)/10000000000),((114872930639656435752500968516115135193071:ℚ)/487200107376000000000000000000000000000000),((2109228134424034975442492071:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((335808671:ℚ)/500000000),((865501083:ℚ)/1250000000),((-198500361:ℚ)/526562500),((-1454660697:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((304420051:ℚ)/625000000),((1141755920364583652354600863866229838978982316247255843:ℚ)/4840321976864337921142578125000000000000000000000000000),((5024106150871434106563719:ℚ)/36966400000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((1709081129:ℚ)/2500000000),((6984062951:ℚ)/10000000000),((-4824062951:ℚ)/12875000000),((-1069081129:ℚ)/3712500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4521350363:ℚ)/10000000000),((1074024613668487569084636059618444861050143161933591756339:ℚ)/4596154973173141479492187500000000000000000000000000000000),((119314937351507592495339319:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1724095131:ℚ)/2500000000),((3522052363:ℚ)/5000000000),((-2442052363:ℚ)/6496875000),((-7588665917:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1084241787:ℚ)/2500000000),((1908630995555335353650578159934143959822031886228666603033:ℚ)/8164555524400520324707031250000000000000000000000000000000),((965212208276996928934277:ℚ)/7680000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((1739105997:ℚ)/2500000000),((7104134333:ℚ)/10000000000),((-4944134333:ℚ)/13112500000),((-7693741979:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2072485789:ℚ)/5000000000),((202312197622833830795218224702967750726471255665091718388801:ℚ)/865078217822961425781250000000000000000000000000000000000000),((338890615053864399953528093:ℚ)/2772480000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((7016455253:ℚ)/10000000000),((3582076053:ℚ)/5000000000),((-2502076053:ℚ)/6615625000),((-31195186771:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3944246881:ℚ)/10000000000),((26829576607021087310247921139481422208739673586488808619391:ℚ)/114673391404072570800781250000000000000000000000000000000000),((1756222994859126742212046031:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((7076474653:ℚ)/10000000000),((3612079181:ℚ)/5000000000),((-2532079181:ℚ)/6675000000),((-31615322571:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3733379879:ℚ)/10000000000),((242466790738300348650799029263982876960417027062955321643787:ℚ)/1035880415930566406250000000000000000000000000000000000000000),((1704774256753567323532653631:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7136482507:ℚ)/10000000000),((7284153411:ℚ)/10000000000),((-5124153411:ℚ)/13468750000),((-32035377549:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((702107539:ℚ)/2000000000),((4225342485889423718846149886488580365004929246308601969805479:ℚ)/18043508188796806335449218750000000000000000000000000000000000),((1653070281028257873143717391:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((57571833:ℚ)/80000000),((146882751:ℚ)/200000000),((-103682751:ℚ)/271750000),((-259642831:ℚ)/877200000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((818317359:ℚ)/2500000000),((981407342326481796513767963570136375723677166839273731:ℚ)/4188933316336566162109375000000000000000000000000000000),((307413302698462430758853:ℚ)/2839019520000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((1451292961:ℚ)/2000000000),((3702055533:ℚ)/5000000000),((-874018511:ℚ)/2284375000),((-939292961:ℚ)/3160000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((754542093:ℚ)/2500000000),((10138767221149508118386835647345899585981197401900295517:ℚ)/43254164899444580078125000000000000000000000000000000000),((61955846286796969073919239:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((1463287967:ℚ)/2000000000),((3762013663:ℚ)/5000000000),((-383144809:ℚ)/987500000),((-739890641:ℚ)/2500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1370125859:ℚ)/5000000000),((1424422645047292352238989950791834126016758595639829:ℚ)/6018542480468750000000000000000000000000000000000000),((59857031607674983461231751:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((7436359043:ℚ)/10000000000),((7643904293:ℚ)/10000000000),((-5483904293:ℚ)/14062500000),((-34134513301:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((83156567:ℚ)/400000000),((21047738499960828907623832700908395978167140229217411781657:ℚ)/88854557275772094726562500000000000000000000000000000000000),((1390717930005001653674494591:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((3778119429:ℚ)/5000000000),((8601716237:ℚ)/10000000000),((-585610567:ℚ)/1300000000),((-17486836003:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((536823033:ℚ)/5000000000),((1992089883696151921534672074360903451156993157424878609:ℚ)/7507560937500000000000000000000000000000000000000000000),((2667562153528143742218437:ℚ)/30720000000000000000000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((4257035253:ℚ)/5000000000),((10512848841:ℚ)/10000000000),((-2784282947:ℚ)/5400000000),((-20839246771:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((62904025647143266255317721258180739363:ℚ)/216000000000000000000000000000000000000),((3448093:ℚ)/40960000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10425231093:ℚ)/10000000000),((14325870843:ℚ)/10000000000),((-12165870843:ℚ)/20000000000),((-55056617651:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8281108218461039150879146579:ℚ)/24376320000000000000000000000),((3448093:ℚ)/40960000)⟩
theorem valid14 : Valid source29 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((45:ℚ)/64) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC09
#check @N11Formalization.C450Source29GroupedC09.bound
#print axioms N11Formalization.C450Source29GroupedC09.valid0
#print axioms N11Formalization.C450Source29GroupedC09.valid1
#print axioms N11Formalization.C450Source29GroupedC09.valid2
#print axioms N11Formalization.C450Source29GroupedC09.valid3
#print axioms N11Formalization.C450Source29GroupedC09.valid4
#print axioms N11Formalization.C450Source29GroupedC09.valid5
#print axioms N11Formalization.C450Source29GroupedC09.valid6
#print axioms N11Formalization.C450Source29GroupedC09.valid7
#print axioms N11Formalization.C450Source29GroupedC09.valid8
#print axioms N11Formalization.C450Source29GroupedC09.valid9
#print axioms N11Formalization.C450Source29GroupedC09.valid10
#print axioms N11Formalization.C450Source29GroupedC09.valid11
#print axioms N11Formalization.C450Source29GroupedC09.valid12
#print axioms N11Formalization.C450Source29GroupedC09.valid13
#print axioms N11Formalization.C450Source29GroupedC09.valid14
#print axioms N11Formalization.C450Source29GroupedC09.bound
#print axioms N11Formalization.C450Source29GroupedC09.endpoint_checks
