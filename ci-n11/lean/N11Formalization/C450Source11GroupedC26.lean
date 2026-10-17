import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((2971066051:ℚ)/5000000000),((404116279:ℚ)/625000000),((9873198153:ℚ)/17800000000),((444116279:ℚ)/620000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((420720943:ℚ)/625000000),((-11936276431382421418587581630507971:ℚ)/1409938000000000000000000000000000000),((-8088323171501664110044681:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6417692627:ℚ)/10000000000),((3351794401:ℚ)/5000000000),((63519233643:ℚ)/110600000000),((1223931467:ℚ)/1780000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5652901009:ℚ)/10000000000),((-97136290477807879533874473203357869229587527647719167243:ℚ)/8455618850000000000000000000000000000000000000000000000000),((-32575246078704784566169449:ℚ)/184832000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((1331088791:ℚ)/2000000000),((3411223589:ℚ)/5000000000),((1459088791:ℚ)/2500000000),((3731223589:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((503878923:ℚ)/1000000000),((-1256223083179685959398513420234591398549340443148951:ℚ)/97656250000000000000000000000000000000000000000000000),((-1307507711795921565078161:ℚ)/7393280000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((3387156621:ℚ)/5000000000),((6941301949:ℚ)/10000000000),((33364409589:ℚ)/57200000000),((7581301949:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((470466311:ℚ)/1000000000),((-1377305615999364369543339727018731916762707883808032679:ℚ)/106334800000000000000000000000000000000000000000000000000),((-24558212971015862804112763:ℚ)/138624000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((3446589281:ℚ)/5000000000),((7000728039:ℚ)/10000000000),((11299767843:ℚ)/19225000000),((7640728039:ℚ)/11440000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1086745521:ℚ)/2500000000),((-150888232780318764477788247079995800987002867674905763:ℚ)/11102456274414062500000000000000000000000000000000000000),((-8200280108567655165515841:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1390521959:ℚ)/2000000000),((7060153293:ℚ)/10000000000),((13666697631:ℚ)/23260000000),((7700153293:ℚ)/11535000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((415741563:ℚ)/1000000000),((-42855066364210336985885447796026676533282373482973239:ℚ)/3146075494000000000000000000000000000000000000000000000),((-1313185227281254392914161:ℚ)/7393280000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((9:ℚ)/16),((5:ℚ)/8),((1753010027:ℚ)/2500000000),((7119577731:ℚ)/10000000000),((17217090243:ℚ)/29312500000),((7759577731:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3959337271:ℚ)/10000000000),((-76744682698337605163480724340019484070680043738274421:ℚ)/5621866989135742187500000000000000000000000000000000000),((-2053637642611493912117049:ℚ)/11552000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7071469523:ℚ)/10000000000),((3589500687:ℚ)/5000000000),((23134408569:ℚ)/39400000000),((3909500687:ℚ)/5862500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((468924381:ℚ)/1250000000),((-1307227064140062087280851625832544664112815020368032889:ℚ)/95567162500000000000000000000000000000000000000000000000),((-32886835241269518317567849:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((7130898063:ℚ)/10000000000),((90480303:ℚ)/125000000),((69938082567:ℚ)/119150000000),((98480303:ℚ)/147750000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1765921527:ℚ)/5000000000),((-144884148843171104472432502597973360835733861027017909447:ℚ)/10572121786718750000000000000000000000000000000000000000000),((-98746588706413120839122467:ℚ)/554496000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7190325747:ℚ)/10000000000),((7297846349:ℚ)/10000000000),((70472931723:ℚ)/120100000000),((7937846349:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3298359411:ℚ)/10000000000),((-9289828102966357833957145499509273511843400716286004883:ℚ)/676688906640625000000000000000000000000000000000000000000),((-98832855812588226507480187:ℚ)/554496000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((3624876299:ℚ)/5000000000),((7357267717:ℚ)/10000000000),((3944876299:ℚ)/6725000000),((7997267717:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3047739301:ℚ)/10000000000),((-26138497083896029557831055741317121839002008464609811:ℚ)/1900889550781250000000000000000000000000000000000000000),((-8243275588984925371071481:ℚ)/46208000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((7309178633:ℚ)/10000000000),((3708344181:ℚ)/5000000000),((71542607697:ℚ)/122000000000),((4028344181:ℚ)/6052500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2775339193:ℚ)/10000000000),((-156291422778158859384796102269701481317605147481750116897:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-33001980829707159252281809:ℚ)/184832000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((230268871:ℚ)/312500000),((7535527549:ℚ)/10000000000),((750806613:ℚ)/1290625000),((8175527549:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((309246199:ℚ)/1250000000),((-44590013495500272757198835849751159939321044652293:ℚ)/3359079217910766601562500000000000000000000000000000),((-32256758495478813507921:ℚ)/180500000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7487452037:ℚ)/10000000000),((191359101:ℚ)/250000000),((73147068333:ℚ)/125800000000),((207359101:ℚ)/309750000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((215389461:ℚ)/1250000000),((-161821853988036418336890313100589824094627338549015437:ℚ)/12151278759765625000000000000000000000000000000000000000),((-91659237266405745187249:ℚ)/512000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((7606297233:ℚ)/10000000000),((1578405881:ℚ)/2000000000),((8246297233:ℚ)/14400000000),((1706405881:ℚ)/2516000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-25694391367090942275459951743008281602024537063979353:ℚ)/2073600000000000000000000000000000000000000000000000000),((-11476523:ℚ)/64000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7843979241:ℚ)/10000000000),((9793069333:ℚ)/10000000000),((76355813169:ℚ)/160000000000),((10433069333:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-64101055174968554272274928511353493:ℚ)/24000000000000000000000000000000000000),((-11476523:ℚ)/64000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((9745123809:ℚ)/10000000000),((13594289711:ℚ)/10000000000),((31155371427:ℚ)/73600000000),((14234289711:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3322979540577286362579371:ℚ)/677120000000000000000000000),((-11476523:ℚ)/64000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
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
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC26
#check @N11Formalization.C450Source11GroupedC26.bound
#print axioms N11Formalization.C450Source11GroupedC26.valid0
#print axioms N11Formalization.C450Source11GroupedC26.valid1
#print axioms N11Formalization.C450Source11GroupedC26.valid2
#print axioms N11Formalization.C450Source11GroupedC26.valid3
#print axioms N11Formalization.C450Source11GroupedC26.valid4
#print axioms N11Formalization.C450Source11GroupedC26.valid5
#print axioms N11Formalization.C450Source11GroupedC26.valid6
#print axioms N11Formalization.C450Source11GroupedC26.valid7
#print axioms N11Formalization.C450Source11GroupedC26.valid8
#print axioms N11Formalization.C450Source11GroupedC26.valid9
#print axioms N11Formalization.C450Source11GroupedC26.valid10
#print axioms N11Formalization.C450Source11GroupedC26.valid11
#print axioms N11Formalization.C450Source11GroupedC26.valid12
#print axioms N11Formalization.C450Source11GroupedC26.valid13
#print axioms N11Formalization.C450Source11GroupedC26.valid14
#print axioms N11Formalization.C450Source11GroupedC26.valid15
#print axioms N11Formalization.C450Source11GroupedC26.valid16
#print axioms N11Formalization.C450Source11GroupedC26.bound
#print axioms N11Formalization.C450Source11GroupedC26.endpoint_checks
