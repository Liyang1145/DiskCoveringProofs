import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((3040712179:ℚ)/5000000000),((1649497391:ℚ)/2500000000),((4960712179:ℚ)/26700000000),((7028492173:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((12562279:ℚ)/19531250),((3005946864408256617777290873877374514413:ℚ)/90614212224000000000000000000000000000000),((-119927851150406842646711841:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6557928703:ℚ)/10000000000),((3418037713:ℚ)/5000000000),((10397928703:ℚ)/55300000000),((14414113139:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((165576601:ℚ)/312500000),((27132087441710455239441778717105702101069664880242774473602257:ℚ)/873122752930050000000000000000000000000000000000000000000000000),((-503358118846861549770725409:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((679610301:ℚ)/1000000000),((6955103463:ℚ)/10000000000),((354536767:ℚ)/1875000000),((29185310389:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2320507863:ℚ)/5000000000),((109504899605055294214774457938992566803494834692448387241:ℚ)/3623836650000000000000000000000000000000000000000000000000),((-108458183482622372097608811:ℚ)/778240000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((1728793253:ℚ)/2500000000),((7074122233:ℚ)/10000000000),((2688793253:ℚ)/14300000000),((29542366699:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4277746403:ℚ)/10000000000),((5462504693149826443501825586728558443460735047794171436928411:ℚ)/181974133300781250000000000000000000000000000000000000000000000),((-2084240229475445029480388529:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((7034232343:ℚ)/10000000000),((7133628287:ℚ)/10000000000),((10874232343:ℚ)/57675000000),((29720884861:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3882924889:ℚ)/10000000000),((123073512053627412755636950700440168901328557820900788638458527:ℚ)/4150228741744800000000000000000000000000000000000000000000000000),((-2107868331668247595428449409:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((7093758173:ℚ)/10000000000),((224785381:ℚ)/312500000),((10933758173:ℚ)/58150000000),((934356143:ℚ)/3604687500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3670522839:ℚ)/10000000000),((156127668364045891010057242028380374205850359882201368409:ℚ)/5279357172877015113830566406250000000000000000000000000000),((-2069952962664647634939921:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/8),((3:ℚ)/16),((7153281529:ℚ)/10000000000),((3626317001:ℚ)/5000000000),((10993281529:ℚ)/58625000000),((15038951003:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3445686277:ℚ)/10000000000),((5980003834217698630617036410542400946297090359535117817393921:ℚ)/202738450703828320312500000000000000000000000000000000000000000),((-532848506516724814458958161:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((901600309:ℚ)/1250000000),((914016721:ℚ)/1250000000),((1381600309:ℚ)/7387500000),((3782050163:ℚ)/14656250000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3205795337:ℚ)/10000000000),((251511789998585499826673966916345619442236990873118677867:ℚ)/8548059245538711547851562500000000000000000000000000000000),((-33486795636240891228730401:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((363616053:ℚ)/500000000),((3715563679:ℚ)/5000000000),((555616053:ℚ)/3002500000),((15306691037:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((184198197:ℚ)/625000000),((164850309691586601092455992310496029940477917009590583094898631:ℚ)/5582769915665081250000000000000000000000000000000000000000000000),((-538703127403905323601665601:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7391351399:ℚ)/10000000000),((7550113339:ℚ)/10000000000),((11231351399:ℚ)/61000000000),((30970340017:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2348629787:ℚ)/10000000000),((1184393043727573648894278952636023900603338116336468707784017:ℚ)/40287350745756250000000000000000000000000000000000000000000000),((-2178326280370797932907520281:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((469398311:ℚ)/625000000),((8025987883:ℚ)/10000000000),((709398311:ℚ)/4050000000),((32397963649:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((192161081:ℚ)/1250000000),((187594635615312288059296322255902888766439378629336406462667:ℚ)/6205093087500000000000000000000000000000000000000000000000000),((-2263525128436137:ℚ)/15200000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7986379403:ℚ)/10000000000),((1985730713:ℚ)/2000000000),((11826379403:ℚ)/80000000000),((7621192139:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((668258182290751379977154556090598683865791620151671137:ℚ)/20407334400000000000000000000000000000000000000000000000),((-153727011:ℚ)/1024000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9889446791:ℚ)/10000000000),((13731780163:ℚ)/10000000000),((13729446791:ℚ)/110400000000),((49515340489:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((63918727245610691325572450565668039156209:ℚ)/1625088000000000000000000000000000000000000),((-153727011:ℚ)/1024000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC19
#check @N11Formalization.C450Source14GroupedC19.bound
#print axioms N11Formalization.C450Source14GroupedC19.valid0
#print axioms N11Formalization.C450Source14GroupedC19.valid1
#print axioms N11Formalization.C450Source14GroupedC19.valid2
#print axioms N11Formalization.C450Source14GroupedC19.valid3
#print axioms N11Formalization.C450Source14GroupedC19.valid4
#print axioms N11Formalization.C450Source14GroupedC19.valid5
#print axioms N11Formalization.C450Source14GroupedC19.valid6
#print axioms N11Formalization.C450Source14GroupedC19.valid7
#print axioms N11Formalization.C450Source14GroupedC19.valid8
#print axioms N11Formalization.C450Source14GroupedC19.valid9
#print axioms N11Formalization.C450Source14GroupedC19.valid10
#print axioms N11Formalization.C450Source14GroupedC19.valid11
#print axioms N11Formalization.C450Source14GroupedC19.valid12
#print axioms N11Formalization.C450Source14GroupedC19.bound
#print axioms N11Formalization.C450Source14GroupedC19.endpoint_checks
