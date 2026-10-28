import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6308069139:ℚ)/10000000000),((1304327373:ℚ)/2000000000),((-216327373:ℚ)/4960000000),((3475792583:ℚ)/99200000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5916723323:ℚ)/10000000000),((-4862728219712658255303300109775017:ℚ)/238328000000000000000000000000000000),((-146104392820197162927759801:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((401862087:ℚ)/625000000),((103799429:ℚ)/156250000),((-18799429:ℚ)/394921875),((194413739:ℚ)/6318750000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1405776713:ℚ)/2500000000),((-814776018285621356571692343993191879534868525779:ℚ)/48119776463136076927185058593750000000000000000000),((-666564151186153681340289:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1637850979:ℚ)/2500000000),((6703887377:ℚ)/10000000000),((-1263887377:ℚ)/25750000000),((686447063:ℚ)/25750000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((132885343:ℚ)/250000000),((-3292887649945481605126259039083457006862500958123663:ℚ)/208421134948730468750000000000000000000000000000000000),((-12208334728216496006202521:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6612168573:ℚ)/10000000000),((3382293021:ℚ)/5000000000),((-662293021:ℚ)/12993750000),((2563494281:ℚ)/103950000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2577745091:ℚ)/5000000000),((-420974407815780871624019498083465648190469884021789:ℚ)/29678473663330078125000000000000000000000000000000000),((-207738921092637088617429849:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1334581437:ℚ)/2000000000),((6825260163:ℚ)/10000000000),((-1385260163:ℚ)/26225000000),((476255689:ℚ)/20980000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((998198271:ℚ)/2000000000),((-710750528729291849672140769741691236013433825649482797:ℚ)/56363312939453125000000000000000000000000000000000000000),((-8807360650648955603401689:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6733620487:ℚ)/10000000000),((6885910421:ℚ)/10000000000),((-1445910421:ℚ)/26462500000),((2199138539:ℚ)/105850000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4821442907:ℚ)/10000000000),((-480981898611710176820054686560326020203986325026015017:ℚ)/43431406919860839843750000000000000000000000000000000000),((-232668734904918524248069889:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((106161081:ℚ)/156250000),((1736634369:ℚ)/2500000000),((-376634369:ℚ)/6675000000),((31516757:ℚ)/1668750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((92925719:ℚ)/200000000),((-26699853126501903115473932761562397273857052813669053:ℚ)/2788207470703125000000000000000000000000000000000000000),((-59861612971783738658241:ℚ)/902500000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((1713743489:ℚ)/2500000000),((3503570981:ℚ)/5000000000),((-783570981:ℚ)/13468750000),((458769533:ℚ)/26937500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2232427121:ℚ)/5000000000),((-61946669660937956250423056513557549440198249824988491:ℚ)/7635401821136474609375000000000000000000000000000000000),((-16109837399251770199035601:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((6915615457:ℚ)/10000000000),((883465561:ℚ)/1250000000),((-203465561:ℚ)/3396875000),((1653153629:ℚ)/108700000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((267271429:ℚ)/625000000),((-153514950516411824241665051601936267223689888744173:ℚ)/22966244870424270629882812500000000000000000000000000),((-270361513124161772864429969:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((6976234317:ℚ)/10000000000),((1425657129:ℚ)/2000000000),((-337657129:ℚ)/5482500000),((1471297049:ℚ)/109650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((203988203:ℚ)/500000000),((-63335890496369752895374765540803104803917820166237:ℚ)/11976157177734375000000000000000000000000000000000000),((-283005591126595645957330809:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((1407366229:ℚ)/2000000000),((7249346099:ℚ)/10000000000),((-1809346099:ℚ)/27650000000),((257901313:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1936941601:ℚ)/5000000000),((-18830120743786520288125734916091402700505259105802587:ℚ)/9437074609375000000000000000000000000000000000000000000),((-11827588402131769727984521:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((7157961027:ℚ)/10000000000),((737032763:ℚ)/1000000000),((-193032763:ℚ)/2812500000),((926116919:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3427411783:ℚ)/10000000000),((41262215942038586298049128829739049237240806144683:ℚ)/69522857666015625000000000000000000000000000000000000),((-321178366297929262011660249:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((3639504773:ℚ)/5000000000),((7612069697:ℚ)/10000000000),((-2172069697:ℚ)/28600000000),((281485681:ℚ)/57200000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2916720359:ℚ)/10000000000),((368482457801690653006108721432815431106594848864906419:ℚ)/54828881250000000000000000000000000000000000000000000000),((-86707011903240233867731049:ℚ)/924160000000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((940089089:ℚ)/1250000000),((7853540833:ℚ)/10000000000),((-804513611:ℚ)/9850000000),((-20267267:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1807167:ℚ)/12500000),((100410842838845982080507349782686070376271824534712513:ℚ)/8959421484375000000000000000000000000000000000000000000),((-6227761883861958604776401:ℚ)/57760000000000000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((1940516667:ℚ)/2500000000),((4167884297:ℚ)/5000000000),((-1447884297:ℚ)/15250000000),((-221550001:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((60800498168881027981536615672498059208471741891221593:ℚ)/2770764160156250000000000000000000000000000000000000000),((-28788563:ℚ)/256000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8244081609:ℚ)/10000000000),((10257699029:ℚ)/10000000000),((-4817699029:ℚ)/32400000000),((-2332244827:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1282030849783606556510563251205991281994614504929371903:ℚ)/19929037500000000000000000000000000000000000000000000000),((-28788563:ℚ)/256000000)⟩
theorem valid15 : Valid source36 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10165369567:ℚ)/10000000000),((14083262543:ℚ)/10000000000),((-8643262543:ℚ)/40000000000),((-8096108701:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1036411930694376340138939351878498521:ℚ)/8000000000000000000000000000000000000),((-28788563:ℚ)/256000000)⟩
theorem valid16 : Valid source36 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC13
#check @N11Formalization.C450Source36GroupedC13.bound
#print axioms N11Formalization.C450Source36GroupedC13.valid0
#print axioms N11Formalization.C450Source36GroupedC13.valid1
#print axioms N11Formalization.C450Source36GroupedC13.valid2
#print axioms N11Formalization.C450Source36GroupedC13.valid3
#print axioms N11Formalization.C450Source36GroupedC13.valid4
#print axioms N11Formalization.C450Source36GroupedC13.valid5
#print axioms N11Formalization.C450Source36GroupedC13.valid6
#print axioms N11Formalization.C450Source36GroupedC13.valid7
#print axioms N11Formalization.C450Source36GroupedC13.valid8
#print axioms N11Formalization.C450Source36GroupedC13.valid9
#print axioms N11Formalization.C450Source36GroupedC13.valid10
#print axioms N11Formalization.C450Source36GroupedC13.valid11
#print axioms N11Formalization.C450Source36GroupedC13.valid12
#print axioms N11Formalization.C450Source36GroupedC13.valid13
#print axioms N11Formalization.C450Source36GroupedC13.valid14
#print axioms N11Formalization.C450Source36GroupedC13.valid15
#print axioms N11Formalization.C450Source36GroupedC13.valid16
#print axioms N11Formalization.C450Source36GroupedC13.bound
#print axioms N11Formalization.C450Source36GroupedC13.endpoint_checks
