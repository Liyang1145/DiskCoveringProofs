import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((5917285347:ℚ)/10000000000),((3222057361:ℚ)/5000000000),((6797285347:ℚ)/13350000000),((32838516249:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6783802639:ℚ)/10000000000),((-301514956435528705254448299338281:ℚ)/118963518750000000000000000000000000),((-750714909465459972186377417:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((31965959:ℚ)/50000000),((6681989299:ℚ)/10000000000),((5195137:ℚ)/9875000),((22605967897:ℚ)/35600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5712802023:ℚ)/10000000000),((-21876091091432728769480812317065265075951899:ℚ)/3611125488281250000000000000000000000000000000),((-18984864933494324544753:ℚ)/92416000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6631098189:ℚ)/10000000000),((6800917077:ℚ)/10000000000),((7511098189:ℚ)/14062500000),((9841179099:ℚ)/15800000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2552370963:ℚ)/5000000000),((-8853066349841958944231633249442270934729371094416007:ℚ)/1158714294433593750000000000000000000000000000000000000),((-763748346665081057895791273:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((6750041063:ℚ)/10000000000),((864979867:ℚ)/1250000000),((7630041063:ℚ)/14300000000),((2914939601:ℚ)/4687500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4774636597:ℚ)/10000000000),((-2581111470773042045541890005355992228500546756403253:ℚ)/332296250000000000000000000000000000000000000000000000),((-765928721454083535190515697:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1373795503:ℚ)/2000000000),((7038755169:ℚ)/10000000000),((1549795503:ℚ)/2907500000),((71028796521:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4421990111:ℚ)/10000000000),((-60534730898298921464429807073896154227338171478727:ℚ)/7680848374023437500000000000000000000000000000000000),((-30724457500307158838781217:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/2),((9:ℚ)/16),((3493953931:ℚ)/5000000000),((354910563:ℚ)/500000000),((3933953931:ℚ)/7328125000),((3578195067:ℚ)/5815000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((252554681:ℚ)/625000000),((-150762180943050948348877134712279814226370075070397:ℚ)/17568334341049194335937500000000000000000000000000000),((-192574125063739085109516793:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3523685419:ℚ)/5000000000),((3578833023:ℚ)/5000000000),((1321228473:ℚ)/2462500000),((36049497207:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((767401281:ℚ)/2000000000),((-40230712998855529183857948826778569278175127358473:ℚ)/4666365356445312500000000000000000000000000000000000),((-192847478302571899414923193:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((7106832397:ℚ)/10000000000),((7217119557:ℚ)/10000000000),((7986832397:ℚ)/14893750000),((24211358671:ℚ)/39400000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((724456613:ℚ)/2000000000),((-107273188894959668830486178036219196185927766206638879:ℚ)/12389205218811035156250000000000000000000000000000000000),((-772483914709551118765375017:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((7166292573:ℚ)/10000000000),((7276571823:ℚ)/10000000000),((8046292573:ℚ)/15012500000),((73169146407:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3394641381:ℚ)/10000000000),((-2297854626301317262476049855321368915324600206400437:ℚ)/264331604156494140625000000000000000000000000000000000),((-773578505334883702507074377:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((3612875699:ℚ)/5000000000),((3668011437:ℚ)/5000000000),((4052875699:ℚ)/7565625000),((36852102933:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((630255689:ℚ)/2000000000),((-58306985835356399318020048466319543003952491374459:ℚ)/6682814826965332031250000000000000000000000000000000),((-193668421408245052206028713:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((1457041781:ℚ)/2000000000),((7395472739:ℚ)/10000000000),((1633041781:ℚ)/3050000000),((24746418217:ℚ)/40350000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2888218009:ℚ)/10000000000),((-310473909837897101042025299041973138578197287450061:ℚ)/35465781250000000000000000000000000000000000000000000),((-31030778246811761930886393:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((58757321:ℚ)/80000000),((3757184509:ℚ)/5000000000),((65797321:ℚ)/123900000),((37654660581:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((649870381:ℚ)/2500000000),((-1627894349397966721417888003615554960107767067:ℚ)/198126554062500000000000000000000000000000000000),((-49719412318576246724433:ℚ)/236584960000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((373178691:ℚ)/500000000),((763326087:ℚ)/1000000000),((24539923:ℚ)/46250000),((2545978261:ℚ)/4130000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1897618353:ℚ)/10000000000),((-999124232250143796851017452763163631817763:ℚ)/120766162872314453125000000000000000000000000),((-1947650785963781969654153:ℚ)/9241600000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((473904857:ℚ)/625000000),((314841283:ℚ)/400000000),((176301619:ℚ)/337500000),((3140771547:ℚ)/5032000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((339591719:ℚ)/5000000000),((-12935827164587002064849394721372142696049874673:ℚ)/1779785156250000000000000000000000000000000000000),((-3051785860459364433993937:ℚ)/14440000000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3910135967:ℚ)/5000000000),((1954547473:ℚ)/2000000000),((4350135967:ℚ)/10000000000),((6375642419:ℚ)/8640000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1328649195265130984103708595519727:ℚ)/375000000000000000000000000000000000),((-54126117:ℚ)/256000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((4861060947:ℚ)/5000000000),((1357473813:ℚ)/1000000000),((5301060947:ℚ)/13800000000),((12985264317:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1253609667169797629823599:ℚ)/95220000000000000000000000),((-54126117:ℚ)/256000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC25
#check @N11Formalization.C450Source13GroupedC25.bound
#print axioms N11Formalization.C450Source13GroupedC25.valid0
#print axioms N11Formalization.C450Source13GroupedC25.valid1
#print axioms N11Formalization.C450Source13GroupedC25.valid2
#print axioms N11Formalization.C450Source13GroupedC25.valid3
#print axioms N11Formalization.C450Source13GroupedC25.valid4
#print axioms N11Formalization.C450Source13GroupedC25.valid5
#print axioms N11Formalization.C450Source13GroupedC25.valid6
#print axioms N11Formalization.C450Source13GroupedC25.valid7
#print axioms N11Formalization.C450Source13GroupedC25.valid8
#print axioms N11Formalization.C450Source13GroupedC25.valid9
#print axioms N11Formalization.C450Source13GroupedC25.valid10
#print axioms N11Formalization.C450Source13GroupedC25.valid11
#print axioms N11Formalization.C450Source13GroupedC25.valid12
#print axioms N11Formalization.C450Source13GroupedC25.valid13
#print axioms N11Formalization.C450Source13GroupedC25.valid14
#print axioms N11Formalization.C450Source13GroupedC25.valid15
#print axioms N11Formalization.C450Source13GroupedC25.bound
#print axioms N11Formalization.C450Source13GroupedC25.endpoint_checks
