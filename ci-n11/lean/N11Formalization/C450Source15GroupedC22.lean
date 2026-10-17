import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((5968227899:ℚ)/10000000000),((6494198227:ℚ)/10000000000),((7632227899:ℚ)/21360000000),((23962594681:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6676268593:ℚ)/10000000000),((46673682440806440420657110509033490412187:ℚ)/2174741093376000000000000000000000000000000),((-372025667702180793571222641:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6444782113:ℚ)/10000000000),((6732328681:ℚ)/10000000000),((8108782113:ℚ)/22120000000),((24676986043:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5586005563:ℚ)/10000000000),((1773252391042519950392588599456719680044113681203940298009849:ℚ)/97013639214450000000000000000000000000000000000000000000000000),((-382460840478871042102135769:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((3341489381:ℚ)/5000000000),((54811023:ℚ)/80000000),((1391163127:ℚ)/3750000000),((200273069:ℚ)/442400000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4963233409:ℚ)/10000000000),((11758620382356624802300544335620437570763439401163:ℚ)/695776636800000000000000000000000000000000000000000),((-24811061795224621977641:ℚ)/118292480000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((1700514841:ℚ)/2500000000),((1394083419:ℚ)/2000000000),((2116514841:ℚ)/5720000000),((5078250257:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((462347613:ℚ)/1000000000),((337723064310442078720983311180927249523023843923532219113:ℚ)/20219348144531250000000000000000000000000000000000000000000),((-15608149706829826401359969:ℚ)/73932800000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((346056447:ℚ)/500000000),((443090427:ℚ)/625000000),((429256447:ℚ)/1163000000),((1609271281:ℚ)/3575000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((10647041:ℚ)/25000000),((1595838785626462230283233953041545088614005449921091279041:ℚ)/96562298285717773437500000000000000000000000000000000000000),((-1534108901761605710997841:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/16),((3:ℚ)/8),((3520094017:ℚ)/5000000000),((446809893:ℚ)/625000000),((4352094017:ℚ)/11725000000),((1620429679:ℚ)/3634375000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((772434851:ℚ)/2000000000),((263045126626992898403536713970554702268168328021017256279:ℚ)/16498897355454778671264648437500000000000000000000000000000),((-1544271618974399265201321:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((709971381:ℚ)/1000000000),((901058443:ℚ)/1250000000),((876371381:ℚ)/2364000000),((3263175329:ℚ)/7328125000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3648623969:ℚ)/10000000000),((6819400070139247528485820174732994907926040388475799969343:ℚ)/429539977088320255279541015625000000000000000000000000000000),((-6196809783670059685007521:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((7159237153:ℚ)/10000000000),((1816993663:ℚ)/2500000000),((8823237153:ℚ)/23830000000),((6570980989:ℚ)/14775000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3422411961:ℚ)/10000000000),((603409820095689307600565636643988037654651688051676612512583:ℚ)/38158326172262988281250000000000000000000000000000000000000000),((-24866089603027202036657801:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((3609379061:ℚ)/5000000000),((7327479663:ℚ)/10000000000),((4441379061:ℚ)/12010000000),((26462438989:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((795208321:ℚ)/2500000000),((1876952401173886954612281918925468230456104830254743588493461:ℚ)/119134679978788372802734375000000000000000000000000000000000000),((-399118358266585052273501801:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((7278276773:ℚ)/10000000000),((7446483591:ℚ)/10000000000),((8942276773:ℚ)/24400000000),((26819450773:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((292007151:ℚ)/1000000000),((81129601304353580692806055049039249202445278944510907585013:ℚ)/5035918843219531250000000000000000000000000000000000000000000),((-21068411062652365133621571:ℚ)/97280000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((369865367:ℚ)/500000000),((3842234183:ℚ)/5000000000),((453065367:ℚ)/1258000000),((13766702549:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2314713211:ℚ)/10000000000),((294400640819779376270386666599297715747977146094822090338701:ℚ)/17539646449414062500000000000000000000000000000000000000000000),((-529960871633489:ℚ)/2432000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((7635342963:ℚ)/10000000000),((7922424631:ℚ)/10000000000),((9299342963:ℚ)/25920000000),((28247273893:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((169351187586401465906062825713037939877549443241625149348077:ℚ)/10204741112681250000000000000000000000000000000000000000000000),((-28208327:ℚ)/128000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((7873347077:ℚ)/10000000000),((153520201:ℚ)/156250000),((9537347077:ℚ)/32000000000),((530560603:ℚ)/1012500000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((30975707077507226687510122892416531:ℚ)/1280000000000000000000000000000000000),((-28208327:ℚ)/128000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((4888257953:ℚ)/5000000000),((851791051:ℚ)/625000000),((1906752651:ℚ)/7360000000),((2835373153:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((920160605169044487626609:ℚ)/27084800000000000000000000),((-28208327:ℚ)/128000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC22
#check @N11Formalization.C450Source15GroupedC22.bound
#print axioms N11Formalization.C450Source15GroupedC22.valid0
#print axioms N11Formalization.C450Source15GroupedC22.valid1
#print axioms N11Formalization.C450Source15GroupedC22.valid2
#print axioms N11Formalization.C450Source15GroupedC22.valid3
#print axioms N11Formalization.C450Source15GroupedC22.valid4
#print axioms N11Formalization.C450Source15GroupedC22.valid5
#print axioms N11Formalization.C450Source15GroupedC22.valid6
#print axioms N11Formalization.C450Source15GroupedC22.valid7
#print axioms N11Formalization.C450Source15GroupedC22.valid8
#print axioms N11Formalization.C450Source15GroupedC22.valid9
#print axioms N11Formalization.C450Source15GroupedC22.valid10
#print axioms N11Formalization.C450Source15GroupedC22.valid11
#print axioms N11Formalization.C450Source15GroupedC22.valid12
#print axioms N11Formalization.C450Source15GroupedC22.valid13
#print axioms N11Formalization.C450Source15GroupedC22.bound
#print axioms N11Formalization.C450Source15GroupedC22.endpoint_checks
