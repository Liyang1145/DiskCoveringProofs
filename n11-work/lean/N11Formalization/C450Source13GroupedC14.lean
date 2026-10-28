import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((124792239:ℚ)/200000000),((3255105383:ℚ)/5000000000),((-6245316149:ℚ)/49600000000),((-47992239:ℚ)/1030000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3038166099:ℚ)/5000000000),((1767163358292742120252475919063289063978527993746241:ℚ)/42343171250000000000000000000000000000000000000000000),((-6785331946497326050603293:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((6477680999:ℚ)/10000000000),((1349665499:ℚ)/2000000000),((-2640996497:ℚ)/20600000000),((-2637680999:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((275189419:ℚ)/500000000),((202587351645097067370658506030694562569493069517682643233:ℚ)/4901296972500000000000000000000000000000000000000000000000),((-1493562857916274959755237:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6715709419:ℚ)/10000000000),((686736963:ℚ)/1000000000),((-1356210889:ℚ)/10680000000),((-2875709419:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4872025089:ℚ)/10000000000),((2182195733925520331799310521401536052027218844455390232617:ℚ)/53582123328281250000000000000000000000000000000000000000000),((-476084243635736004106453:ℚ)/36966400000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((683470973:ℚ)/1000000000),((6986401691:ℚ)/10000000000),((-13919205073:ℚ)/108700000000),((-299470973:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1131552811:ℚ)/2500000000),((437088060281881448642891801539660978527797645142263617:ℚ)/10771005105410156250000000000000000000000000000000000000),((-52702441542355052160208997:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((1390740283:ℚ)/2000000000),((3522957053:ℚ)/5000000000),((-7048871159:ℚ)/55300000000),((-622740283:ℚ)/11155000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((830771547:ℚ)/2000000000),((2417748764510064844681764663706771714626381380497613411:ℚ)/59968596603740234375000000000000000000000000000000000000),((-14458740065309248838587733:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((7013194161:ℚ)/10000000000),((111022253:ℚ)/156250000),((-223066759:ℚ)/1742968750),((-352577129:ℚ)/6250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3955398133:ℚ)/10000000000),((321184961740232600300772833053811055142081856630355293:ℚ)/7978677749633789062500000000000000000000000000000000000),((-117931259579658683223939:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((442042807:ℚ)/625000000),((7164932009:ℚ)/10000000000),((-14454796027:ℚ)/112500000000),((-202042807:ℚ)/3545312500),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((936757009:ℚ)/2500000000),((50378582602935759429457249514852290106346354914587:ℚ)/1253303050768375396728515625000000000000000000000000),((-62926226080821541036043197:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7132173719:ℚ)/10000000000),((1806109403:ℚ)/2500000000),((-3658328209:ℚ)/28362500000),((-3292173719:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1763493567:ℚ)/5000000000),((21306683194781399557288665852141088876861554002408578979819:ℚ)/530802054640000000000000000000000000000000000000000000000000),((-4091951625436498763756933:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((7191660631:ℚ)/10000000000),((7283941057:ℚ)/10000000000),((-14811823171:ℚ)/114400000000),((-3351660631:ℚ)/57675000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1646466081:ℚ)/5000000000),((14645400156351906386897981412757865759961339477453929:ℚ)/365340201779937744140625000000000000000000000000000000),((-68015806812025616607756013:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((3625572847:ℚ)/5000000000),((1835860599:ℚ)/2500000000),((-3747581797:ℚ)/28837500000),((-1705572847:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1520812433:ℚ)/5000000000),((2837706700530692454358204989009142556173231076084643504941:ℚ)/70878868795488281250000000000000000000000000000000000000000),((-4409998155989060733947837:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((1462125791:ℚ)/2000000000),((1492487793:ℚ)/2000000000),((-3069463379:ℚ)/23260000000),((-694125791:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((553673121:ℚ)/2000000000),((891588422950923774392315827027979470103621409903393191:ℚ)/22228921997500000000000000000000000000000000000000000000),((-2922459005039482759819213:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((46434939:ℚ)/62500000),((1895356927:ℚ)/2500000000),((-3926070781:ℚ)/29550000000),((-22434939:ℚ)/375312500),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1060816551:ℚ)/5000000000),((390716066440336946199080635852057751858651147951441:ℚ)/9763748628530502319335937500000000000000000000000000),((-4884191308808907871556973:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((943568103:ℚ)/1250000000),((7700408993:ℚ)/10000000000),((-16061226979:ℚ)/120100000000),((-463568103:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((291077127:ℚ)/2500000000),((26577346518155758841157465585018173113561899015077057823:ℚ)/665537551269531250000000000000000000000000000000000000000),((-2740275878412639:ℚ)/121600000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7667493019:ℚ)/10000000000),((8176266137:ℚ)/10000000000),((-17488798411:ℚ)/122000000000),((-3827493019:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((280339720540730106141862557087483848457691948792037676197:ℚ)/6915818880000000000000000000000000000000000000000000000000),((-5923897:ℚ)/256000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((4071613777:ℚ)/5000000000),((5039439409:ℚ)/5000000000),((-11598318227:ℚ)/64800000000),((-2151613777:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((276322158591784398597344652265382513775144763045711292417:ℚ)/6480000000000000000000000000000000000000000000000000000000),((-5923897:ℚ)/256000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((10045466703:ℚ)/10000000000),((13881943303:ℚ)/10000000000),((-34605829909:ℚ)/160000000000),((-2068488901:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2206067098989623361477061775261436825582359150428957247:ℚ)/46721280000000000000000000000000000000000000000000000000),((-5923897:ℚ)/256000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC14
#check @N11Formalization.C450Source13GroupedC14.bound
#print axioms N11Formalization.C450Source13GroupedC14.valid0
#print axioms N11Formalization.C450Source13GroupedC14.valid1
#print axioms N11Formalization.C450Source13GroupedC14.valid2
#print axioms N11Formalization.C450Source13GroupedC14.valid3
#print axioms N11Formalization.C450Source13GroupedC14.valid4
#print axioms N11Formalization.C450Source13GroupedC14.valid5
#print axioms N11Formalization.C450Source13GroupedC14.valid6
#print axioms N11Formalization.C450Source13GroupedC14.valid7
#print axioms N11Formalization.C450Source13GroupedC14.valid8
#print axioms N11Formalization.C450Source13GroupedC14.valid9
#print axioms N11Formalization.C450Source13GroupedC14.valid10
#print axioms N11Formalization.C450Source13GroupedC14.valid11
#print axioms N11Formalization.C450Source13GroupedC14.valid12
#print axioms N11Formalization.C450Source13GroupedC14.valid13
#print axioms N11Formalization.C450Source13GroupedC14.valid14
#print axioms N11Formalization.C450Source13GroupedC14.valid15
#print axioms N11Formalization.C450Source13GroupedC14.bound
#print axioms N11Formalization.C450Source13GroupedC14.endpoint_checks
