import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6528565471:ℚ)/10000000000),((6834259129:ℚ)/10000000000),((-49988332161:ℚ)/99200000000),((-5008565471:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((537440557:ℚ)/1000000000),((49008555085279123850565389296430414410851225845220393557:ℚ)/620261297607421875000000000000000000000000000000000000000),((9999117602326365377025277:ℚ)/40960000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((845903847:ℚ)/1250000000),((6953568521:ℚ)/10000000000),((-51062116689:ℚ)/103000000000),((-655903847:ℚ)/1639062500),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4725179853:ℚ)/10000000000),((27031199238275235939131672615028239694110553467223419:ℚ)/354334792038798332214355468750000000000000000000000000),((55465096870272079131971253:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6886531547:ℚ)/10000000000),((1402643127:ℚ)/2000000000),((-10319788143:ℚ)/20980000000),((-5366531547:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4367703637:ℚ)/10000000000),((569548485216230909608713747903447675803063438387777753693:ℚ)/7593257643155670166015625000000000000000000000000000000000),((3519558451047177914146465853:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((6946174467:ℚ)/10000000000),((56582863:ℚ)/80000000),((-417085767:ℚ)/846800000),((-5426174467:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1044583043:ℚ)/2500000000),((295226060385354324850552738349276164191709581714264534209:ℚ)/3935090143652343750000000000000000000000000000000000000000),((3504391958070582373992336813:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((7005812589:ℚ)/10000000000),((7132495371:ℚ)/10000000000),((-17557486113:ℚ)/35600000000),((-5485812589:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((796105997:ℚ)/2000000000),((597576524351299639144168929827779347980608418367946817:ℚ)/7963485493138432502746582031250000000000000000000000000),((3489183687969078392805609357:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7065446041:ℚ)/10000000000),((7192128249:ℚ)/10000000000),((-53209154241:ℚ)/107750000000),((-5545446041:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1886483469:ℚ)/5000000000),((253582719476318892141061238475429330979907560855522393529:ℚ)/3378671458697509765625000000000000000000000000000000000000),((3473933618340275995503684277:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3562537473:ℚ)/5000000000),((725175663:ℚ)/1000000000),((-5374580967:ℚ)/10870000000),((-2802537473:ℚ)/6853125000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((28431429:ℚ)/80000000),((6839344692202383036738967364781456039538911322944852107:ℚ)/91109629336667060852050781250000000000000000000000000000),((864660431923986129123042693:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((224521857:ℚ)/312500000),((731138063:ℚ)/1000000000),((-1809414189:ℚ)/3655000000),((-2240783:ℚ)/5468750),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1660570243:ℚ)/5000000000),((657450289573697800228069942666427822701231283:ℚ)/8756748866289854049682617187500000000000000000),((3362605463833045813092933:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((724431959:ℚ)/1000000000),((1842750091:ℚ)/2500000000),((-13704750819:ℚ)/27650000000),((-572431959:ℚ)/1394375000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((153573631:ℚ)/500000000),((21987567870674812751543301484247659296276479099233457:ℚ)/292815413104200363159179687500000000000000000000000000),((34279324000210830592552277:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((3651967777:ℚ)/5000000000),((3715307969:ℚ)/5000000000),((-27677771721:ℚ)/55775000000),((-321329753:ℚ)/781250000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2800408377:ℚ)/10000000000),((2925775556136552058690815241822148882065549926190939:ℚ)/38958387449383735656738281250000000000000000000000000),((853128730925062472560874693:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((294541897:ℚ)/400000000),((754983503:ℚ)/1000000000),((-626983503:ℚ)/1250000000),((-233741897:ℚ)/572000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2500994241:ℚ)/10000000000),((44596955232785055197050569733549968942802140602367:ℚ)/584841400000000000000000000000000000000000000000000),((5435288874849055025717653:ℚ)/23658496000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((3741379647:ℚ)/5000000000),((3894113859:ℚ)/5000000000),((-29287024731:ℚ)/57200000000),((-2981379647:ℚ)/7387500000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((43969073:ℚ)/250000000),((30193503689355770157848932144660713541161362460446083:ℚ)/384975141906738281250000000000000000000000000000000000),((841502755129437360989179653:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((3860569121:ℚ)/5000000000),((8026564501:ℚ)/10000000000),((-20239693503:ℚ)/39400000000),((-3100569121:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((64096721752413051367566032299565699990963167347054081089:ℚ)/818760809326171875000000000000000000000000000000000000000),((230977303:ℚ)/1024000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((159189243:ℚ)/200000000),((8503090151:ℚ)/10000000000),((-65007811359:ℚ)/122000000000),((-128789243:ℚ)/324000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((177169308549825871414748247348289842235281901905491:ℚ)/2161193400000000000000000000000000000000000000000000),((230977303:ℚ)/1024000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((527247771:ℚ)/625000000),((10407738289:ℚ)/10000000000),((-9127738289:ℚ)/14400000000),((-432247771:ℚ)/1250000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5495653005971365532003813979356305063214514787531181:ℚ)/54931640625000000000000000000000000000000000000000000),((230977303:ℚ)/1024000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((2068108213:ℚ)/2000000000),((14213186647:ℚ)/10000000000),((-116398679823:ℚ)/160000000000),((-588036071:ℚ)/1840000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((206269825346538858583239084979623980105188710049553968740577:ℚ)/1692800000000000000000000000000000000000000000000000000000000),((230977303:ℚ)/1024000000)⟩
theorem valid15 : Valid source20 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC08
#check @N11Formalization.C450Source20GroupedC08.bound
#print axioms N11Formalization.C450Source20GroupedC08.valid0
#print axioms N11Formalization.C450Source20GroupedC08.valid1
#print axioms N11Formalization.C450Source20GroupedC08.valid2
#print axioms N11Formalization.C450Source20GroupedC08.valid3
#print axioms N11Formalization.C450Source20GroupedC08.valid4
#print axioms N11Formalization.C450Source20GroupedC08.valid5
#print axioms N11Formalization.C450Source20GroupedC08.valid6
#print axioms N11Formalization.C450Source20GroupedC08.valid7
#print axioms N11Formalization.C450Source20GroupedC08.valid8
#print axioms N11Formalization.C450Source20GroupedC08.valid9
#print axioms N11Formalization.C450Source20GroupedC08.valid10
#print axioms N11Formalization.C450Source20GroupedC08.valid11
#print axioms N11Formalization.C450Source20GroupedC08.valid12
#print axioms N11Formalization.C450Source20GroupedC08.valid13
#print axioms N11Formalization.C450Source20GroupedC08.valid14
#print axioms N11Formalization.C450Source20GroupedC08.valid15
#print axioms N11Formalization.C450Source20GroupedC08.bound
#print axioms N11Formalization.C450Source20GroupedC08.endpoint_checks
