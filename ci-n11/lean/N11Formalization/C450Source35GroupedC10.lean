import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3286522251:ℚ)/5000000000),((849284537:ℚ)/1250000000),((-3304991759:ℚ)/12400000000),((-4419566753:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2629482301:ℚ)/5000000000),((429718270928558770778566518573694147:ℚ)/2383280000000000000000000000000000000),((3457875248524931028092963:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6694131111:ℚ)/10000000000),((216102233:ℚ)/312500000),((-852715631:ℚ)/3159375000),((-9202393333:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2466164911:ℚ)/5000000000),((82864953646840946007602247295288313804430091300773:ℚ)/456246769428253173828125000000000000000000000000000),((12958731304862590078577123:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6815129051:ℚ)/10000000000),((3487868701:ℚ)/5000000000),((-13855080907:ℚ)/51500000000),((-1366483879:ℚ)/7425000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4584771907:ℚ)/10000000000),((599543166521332504495581598718748528005394127627964107:ℚ)/3334738159179687500000000000000000000000000000000000000),((12077138412092029330684763:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3437798173:ℚ)/5000000000),((7036183051:ℚ)/10000000000),((-28133281357:ℚ)/103950000000),((-4873394519:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2200797321:ℚ)/5000000000),((609355300347290258050923106689357843807208454001119507:ℚ)/3376750781250000000000000000000000000000000000000000000),((2908257039580392775454627:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3468021659:ℚ)/5000000000),((887076121:ℚ)/1250000000),((-3569532847:ℚ)/13112500000),((-4964064977:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4211062943:ℚ)/10000000000),((2552071582279746473611842288167602944983338022743071007:ℚ)/14090828234863281250000000000000000000000000000000000000),((2796676531007369497457603:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((3498235267:ℚ)/5000000000),((3563407349:ℚ)/5000000000),((-14383851443:ℚ)/52925000000),((-5054705801:ℚ)/26581250000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((4012122933:ℚ)/10000000000),((41755893700297480399683782149688263156918883559204112787:ℚ)/231634170239257812500000000000000000000000000000000000000),((2684542617622143983260307:ℚ)/28880000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((1405335381:ℚ)/2000000000),((7157015699:ℚ)/10000000000),((-28979109893:ℚ)/106325000000),((-2040006143:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3909098817:ℚ)/10000000000),((84797110998323778436693738004098128303452601534074847773:ℚ)/469533094952392578125000000000000000000000000000000000000),((420522879196497213886043:ℚ)/4620800000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((352843927:ℚ)/500000000),((7217403769:ℚ)/10000000000),((-29401826383:ℚ)/106800000000),((-514531781:ℚ)/2693750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3803448999:ℚ)/10000000000),((462935046470268341390486274290568535773391214340834748429:ℚ)/2537888400000000000000000000000000000000000000000000000000),((71242516805844020807:ℚ)/800000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((355863393:ℚ)/500000000),((7277773683:ℚ)/10000000000),((-29824415781:ℚ)/107750000000),((-523590179:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3583334309:ℚ)/10000000000),((1431161505694329669587143038080952715643418040087048647069:ℚ)/7818651464843750000000000000000000000000000000000000000000),((24586128253502240304887:ℚ)/288800000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3588819501:ℚ)/5000000000),((7338125929:ℚ)/10000000000),((-30246881503:ℚ)/108700000000),((-5326458503:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((418689639:ℚ)/1250000000),((92149331676718773987649027580189044436738083349758269823:ℚ)/501705274609375000000000000000000000000000000000000000000),((2344816110356764826408963:ℚ)/28880000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((3618996227:ℚ)/5000000000),((3699230489:ℚ)/5000000000),((-15334613423:ℚ)/54825000000),((-5416988681:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((774722479:ℚ)/2500000000),((163490541074202878644128228920231750310041614429461287:ℚ)/887122753906250000000000000000000000000000000000000000),((2230464316481678169793427:ℚ)/28880000000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((3649164343:ℚ)/5000000000),((3759540641:ℚ)/5000000000),((-15756784487:ℚ)/55300000000),((-5507493029:ℚ)/28125000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2826977413:ℚ)/10000000000),((28343560756434547941275690562792900164559292863789388001:ℚ)/150993193750000000000000000000000000000000000000000000000),((2115557063680887767246987:ℚ)/28880000000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((3709475647:ℚ)/5000000000),((3819819017:ℚ)/5000000000),((-16178733119:ℚ)/56250000000),((-5688426941:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2187116209:ℚ)/10000000000),((23342077048762293234453079791657394579823252688148838599:ℚ)/123596191406250000000000000000000000000000000000000000000),((1884074715389296876629467:ℚ)/28880000000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((7539510271:ℚ)/10000000000),((8602148371:ℚ)/10000000000),((-39095038597:ℚ)/114400000000),((-11738530813:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((631258879:ℚ)/5000000000),((529616749338954366495006325472775538477346634054609227893:ℚ)/2339365600000000000000000000000000000000000000000000000000),((6601465096605842426049683:ℚ)/115520000000000000000000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((4251017983:ℚ)/5000000000),((10519939549:ℚ)/10000000000),((-52519576843:ℚ)/129600000000),((-7313053949:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((74571690093783245095010454678191384203739957661626475361:ℚ)/283435200000000000000000000000000000000000000000000000000),((6791003:ℚ)/128000000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((10419848863:ℚ)/10000000000),((448147053:ℚ)/312500000),((-2477029371:ℚ)/5000000000),((-886067243:ℚ)/4800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((10449256061789688785487286797933567:ℚ)/31250000000000000000000000000000000),((6791003:ℚ)/128000000)⟩
theorem valid15 : Valid source35 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source35 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((45:ℚ)/64) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC10
#check @N11Formalization.C450Source35GroupedC10.bound
#print axioms N11Formalization.C450Source35GroupedC10.valid0
#print axioms N11Formalization.C450Source35GroupedC10.valid1
#print axioms N11Formalization.C450Source35GroupedC10.valid2
#print axioms N11Formalization.C450Source35GroupedC10.valid3
#print axioms N11Formalization.C450Source35GroupedC10.valid4
#print axioms N11Formalization.C450Source35GroupedC10.valid5
#print axioms N11Formalization.C450Source35GroupedC10.valid6
#print axioms N11Formalization.C450Source35GroupedC10.valid7
#print axioms N11Formalization.C450Source35GroupedC10.valid8
#print axioms N11Formalization.C450Source35GroupedC10.valid9
#print axioms N11Formalization.C450Source35GroupedC10.valid10
#print axioms N11Formalization.C450Source35GroupedC10.valid11
#print axioms N11Formalization.C450Source35GroupedC10.valid12
#print axioms N11Formalization.C450Source35GroupedC10.valid13
#print axioms N11Formalization.C450Source35GroupedC10.valid14
#print axioms N11Formalization.C450Source35GroupedC10.valid15
#print axioms N11Formalization.C450Source35GroupedC10.bound
#print axioms N11Formalization.C450Source35GroupedC10.endpoint_checks
