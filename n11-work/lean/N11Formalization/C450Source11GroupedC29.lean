import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((1174122673:ℚ)/2000000000),((6400751459:ℚ)/10000000000),((1270122673:ℚ)/1780000000),((89609768967:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((215033669:ℚ)/312500000),((-322797193957554767303572031030721:ℚ)/11015140625000000000000000000000000),((-58798603275855943715504237:ℚ)/295731200000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((158648143:ℚ)/250000000),((6638397519:ℚ)/10000000000),((511944429:ℚ)/691250000),((92699167747:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2913406519:ℚ)/5000000000),((-69563540052957043269064762884829951721817641240061:ℚ)/2064360070800781250000000000000000000000000000000000),((-916021228665366171670797:ℚ)/4620800000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((3291782893:ℚ)/5000000000),((3378608423:ℚ)/5000000000),((3531782893:ℚ)/4687500000),((6731701357:ℚ)/7900000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5231320827:ℚ)/10000000000),((-7675203693970801999346282979865390017674309387157239:ℚ)/214576721191406250000000000000000000000000000000000000),((-365871932579363189335523797:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((6702382267:ℚ)/10000000000),((1719008467:ℚ)/2500000000),((21547146801:ℚ)/28600000000),((23947110071:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4909350729:ℚ)/10000000000),((-475820667274519691355773188183859076361382015703189491:ℚ)/13291850000000000000000000000000000000000000000000000000),((-1461171648774307294730325317:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3410598269:ℚ)/5000000000),((3497424349:ℚ)/5000000000),((10951794807:ℚ)/14537500000),((48666516537:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4566700311:ℚ)/10000000000),((-171974665358841181083550245970399516892885201015032687:ℚ)/4800530233764648437500000000000000000000000000000000000),((-364714705171188249793574133:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((1735002177:ℚ)/2500000000),((1763563831:ℚ)/2500000000),((795000933:ℚ)/1046875000),((24526329803:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((104957013:ℚ)/250000000),((-65946248604273670939385762575839621392318593145877:ℚ)/1792687177658081054687500000000000000000000000000000),((-273336936124915914874742311:ℚ)/1386240000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6999414037:ℚ)/10000000000),((3556830721:ℚ)/5000000000),((7479414037:ℚ)/9850000000),((49438799373:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4002194061:ℚ)/10000000000),((-54932582482431629154518467859557589729116088632839613:ℚ)/1493236914062500000000000000000000000000000000000000000),((-1456643412341322158270723557:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((7058818877:ℚ)/10000000000),((7173067063:ℚ)/10000000000),((22616456631:ℚ)/29787500000),((99649871819:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3796565933:ℚ)/10000000000),((-6077081845467799980296314724992394296954427500808433879:ℚ)/165189402917480468750000000000000000000000000000000000000),((-76604770752739173499649623:ℚ)/389120000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3559111621:ℚ)/5000000000),((7232472199:ℚ)/10000000000),((11397334863:ℚ)/15012500000),((100422138587:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1789874121:ℚ)/5000000000),((-48622759446328552253634830148902773512773818681524303:ℚ)/1321658020782470703125000000000000000000000000000000000),((-363584672074796243622651973:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((3588813571:ℚ)/5000000000),((3645938431:ℚ)/5000000000),((3828813571:ℚ)/5043750000),((50597199603:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((418695573:ℚ)/1250000000),((-3278101410685790921167742912705180445218356660922531:ℚ)/89104197692871093750000000000000000000000000000000000),((-363296886019442851825245173:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((7237030587:ℚ)/10000000000),((7351281063:ℚ)/10000000000),((23151091761:ℚ)/30500000000),((101966653819:ℚ)/121050000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3103037427:ℚ)/10000000000),((-6523845742083608280748694511987096519530260954540284609:ℚ)/177328906250000000000000000000000000000000000000000000000),((-4356111634213125301714795471:ℚ)/22179840000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((729643359:ℚ)/1000000000),((186752203:ℚ)/250000000),((777643359:ℚ)/1032500000),((2587778639:ℚ)/3050000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((567180567:ℚ)/2000000000),((-61750815942350953515510168024779743661367648962551:ℚ)/1719848559570312500000000000000000000000000000000000),((-43489200007247369138079079:ℚ)/221798400000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((1483047661:ℚ)/2000000000),((1897223363:ℚ)/2500000000),((4737142983:ℚ)/6290000000),((8754634573:ℚ)/10325000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((276190011:ℚ)/1250000000),((-54558713178286831119655016172771315240305880419487:ℚ)/1518909844970703125000000000000000000000000000000000),((-57893736344028676597945813:ℚ)/295731200000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((7534041367:ℚ)/10000000000),((3913249623:ℚ)/5000000000),((8014041367:ℚ)/10800000000),((54072245099:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1318434691:ℚ)/10000000000),((-1110964740797898840568550601312777717770286799488461:ℚ)/32400000000000000000000000000000000000000000000000000),((-4009174787581642061008597:ℚ)/20480000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((388582141:ℚ)/500000000),((9727164601:ℚ)/10000000000),((1237746423:ℚ)/2000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-55886933577144625206512409685220890096563627452727:ℚ)/3125000000000000000000000000000000000000000000000000),((-100237231:ℚ)/512000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((4836140439:ℚ)/5000000000),((6763972751:ℚ)/5000000000),((5076140439:ℚ)/9200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1583830632165581234652252493367837:ℚ)/194672000000000000000000000000000000),((-100237231:ℚ)/512000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source11 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC29
#check @N11Formalization.C450Source11GroupedC29.bound
#print axioms N11Formalization.C450Source11GroupedC29.valid0
#print axioms N11Formalization.C450Source11GroupedC29.valid1
#print axioms N11Formalization.C450Source11GroupedC29.valid2
#print axioms N11Formalization.C450Source11GroupedC29.valid3
#print axioms N11Formalization.C450Source11GroupedC29.valid4
#print axioms N11Formalization.C450Source11GroupedC29.valid5
#print axioms N11Formalization.C450Source11GroupedC29.valid6
#print axioms N11Formalization.C450Source11GroupedC29.valid7
#print axioms N11Formalization.C450Source11GroupedC29.valid8
#print axioms N11Formalization.C450Source11GroupedC29.valid9
#print axioms N11Formalization.C450Source11GroupedC29.valid10
#print axioms N11Formalization.C450Source11GroupedC29.valid11
#print axioms N11Formalization.C450Source11GroupedC29.valid12
#print axioms N11Formalization.C450Source11GroupedC29.valid13
#print axioms N11Formalization.C450Source11GroupedC29.valid14
#print axioms N11Formalization.C450Source11GroupedC29.valid15
#print axioms N11Formalization.C450Source11GroupedC29.bound
#print axioms N11Formalization.C450Source11GroupedC29.endpoint_checks
