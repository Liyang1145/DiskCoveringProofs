import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6387160739:ℚ)/10000000000),((3341915231:ℚ)/5000000000),((-7145745693:ℚ)/24800000000),((-3955160739:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5727461599:ℚ)/10000000000),((69617300095745312175590693695517681978599136215169414851:ℚ)/846863425000000000000000000000000000000000000000000000000),((199160287089022467650193581:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((132521297:ℚ)/200000000),((6922714217:ℚ)/10000000000),((-15008142651:ℚ)/51500000000),((-83881297:ℚ)/427200000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5118280489:ℚ)/10000000000),((512133331448456773644750871641021937740277988403601:ℚ)/6273660124800000000000000000000000000000000000000000),((72022258006586609240549:ℚ)/1182924800000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6864868219:ℚ)/10000000000),((880264939:ℚ)/1250000000),((-640264939:ℚ)/2225000000),((-4432868219:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((443460853:ℚ)/1000000000),((227890763236573039881856670813674040046568294629452924629:ℚ)/2857713244175000000000000000000000000000000000000000000000),((160843793847626356927957821:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((3492117731:ℚ)/5000000000),((3550906787:ℚ)/5000000000),((-7772720361:ℚ)/27175000000),((-2276117731:ℚ)/10965000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((506643387:ℚ)/1250000000),((29431333972019729699237414601673368619067148430091509561:ℚ)/373185041762988281250000000000000000000000000000000000000),((37799360094634370467378221:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7043911:ℚ)/10000000),((7161502111:ℚ)/10000000000),((-5241502111:ℚ)/18275000000),((-4611911:ℚ)/22120000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((192457443:ℚ)/500000000),((91307765959160517529083690841824332805959026033:ℚ)/1158948258628125000000000000000000000000000000000),((146364121237674851381:ℚ)/2957312000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7103581337:ℚ)/10000000000),((3610592633:ℚ)/5000000000),((-7951777899:ℚ)/27650000000),((-4671581337:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3634335593:ℚ)/10000000000),((94400045211730591624484612634705620052871323882226990799:ℚ)/1199371932074804687500000000000000000000000000000000000000),((141524027831414722268939509:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((7163246607:ℚ)/10000000000),((7280863177:ℚ)/10000000000),((-16082589531:ℚ)/55775000000),((-4731246607:ℚ)/22500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1703328591:ℚ)/5000000000),((73179175479965976778193434951494536013019612248126898301:ℚ)/930632972717285156250000000000000000000000000000000000000),((410031453443124643375379567:ℚ)/8871936000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((7222906939:ℚ)/10000000000),((3700101897:ℚ)/5000000000),((-913367299:ℚ)/3125000000),((-368531303:ℚ)/1760000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1581665917:ℚ)/5000000000),((1349661913290647129043102822614103856134819821253233:ℚ)/17036800000000000000000000000000000000000000000000000),((131823482516797889707253181:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3671106643:ℚ)/5000000000),((3759762487:ℚ)/5000000000),((-8399287461:ℚ)/28600000000),((-2455106643:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((326500437:ℚ)/1250000000),((4275569425954539073522318349587540949980785095591444607:ℚ)/54073172553125000000000000000000000000000000000000000000),((30523933993504450291930189:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((1865375333:ℚ)/2500000000),((3819413831:ℚ)/5000000000),((-8578241493:ℚ)/29075000000),((-419125111:ℚ)/1970000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((478005347:ℚ)/2500000000),((548295096232172141765657067800874232508297042800938147:ℚ)/6946538124218750000000000000000000000000000000000000000),((7021295249985830076876029:ℚ)/184832000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((3790385983:ℚ)/5000000000),((1969345263:ℚ)/2500000000),((-1489345263:ℚ)/4925000000),((-2574385983:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((711487461:ℚ)/10000000000),((89432261925841723833199587463683594432864007467282424821:ℚ)/1117881425000000000000000000000000000000000000000000000000),((25639596701945721741295429:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((195481607:ℚ)/250000000),((8354301397:ℚ)/10000000000),((-19302904191:ℚ)/61000000000),((-14964623:ℚ)/72000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1943147343070960595480425254447733852589346977471:ℚ)/23716800000000000000000000000000000000000000000000),((34964907:ℚ)/1024000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((4148036673:ℚ)/5000000000),((10260150377:ℚ)/10000000000),((-8340150377:ℚ)/21600000000),((-2932036673:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((31857771394526823032608910780297011536199394120793716621:ℚ)/345600000000000000000000000000000000000000000000000000000),((34964907:ℚ)/1024000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((1275197979:ℚ)/1250000000),((14067003667:ℚ)/10000000000),((-36441011001:ℚ)/80000000000),((-971197979:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((41405973954603487799689491321383734565653814103723863:ℚ)/394210800000000000000000000000000000000000000000000000),((34964907:ℚ)/1024000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC11
#check @N11Formalization.C450Source20GroupedC11.bound
#print axioms N11Formalization.C450Source20GroupedC11.valid0
#print axioms N11Formalization.C450Source20GroupedC11.valid1
#print axioms N11Formalization.C450Source20GroupedC11.valid2
#print axioms N11Formalization.C450Source20GroupedC11.valid3
#print axioms N11Formalization.C450Source20GroupedC11.valid4
#print axioms N11Formalization.C450Source20GroupedC11.valid5
#print axioms N11Formalization.C450Source20GroupedC11.valid6
#print axioms N11Formalization.C450Source20GroupedC11.valid7
#print axioms N11Formalization.C450Source20GroupedC11.valid8
#print axioms N11Formalization.C450Source20GroupedC11.valid9
#print axioms N11Formalization.C450Source20GroupedC11.valid10
#print axioms N11Formalization.C450Source20GroupedC11.valid11
#print axioms N11Formalization.C450Source20GroupedC11.valid12
#print axioms N11Formalization.C450Source20GroupedC11.valid13
#print axioms N11Formalization.C450Source20GroupedC11.bound
#print axioms N11Formalization.C450Source20GroupedC11.endpoint_checks
