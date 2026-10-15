import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((751794033:ℚ)/1250000000),((3265297027:ℚ)/5000000000),((821794033:ℚ)/1668750000),((31947673243:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3288812189:ℚ)/5000000000),((272314143426515488571:ℚ)/696181640625000000000000),((-83812864137708177755133:ℚ)/640000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6489754491:ℚ)/10000000000),((6768245529:ℚ)/10000000000),((7049754491:ℚ)/13825000000),((66034209761:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2736669139:ℚ)/5000000000),((-70322251038149616019011254324357835029781252373076809:ℚ)/49544641699218750000000000000000000000000000000000000000),((-1957908254889487272168902877:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6727434851:ℚ)/10000000000),((275482697:ℚ)/400000000),((7287434851:ℚ)/14062500000),((2684144273:ℚ)/4424000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4838966617:ℚ)/10000000000),((-12927908960707318846789453030817444456064764333744689:ℚ)/5793571472167968750000000000000000000000000000000000000),((-1968849894660334128582515917:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((855783807:ℚ)/1250000000),((7005886931:ℚ)/10000000000),((71214139:ℚ)/137500000),((68172982379:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2245651401:ℚ)/5000000000),((-3428118261145862076929795464672606237458752353:ℚ)/1477050781250000000000000000000000000000000000000),((-85455729004248816106653:ℚ)/640000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((435318951:ℚ)/625000000),((282611833:ℚ)/400000000),((470318951:ℚ)/901171875),((2748306497:ℚ)/4576000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4116522991:ℚ)/10000000000),((-36951216805830015748074048432331706289622996287181:ℚ)/13722213107720017433166503906250000000000000000000000),((-7734065376387075046135317:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1756129643:ℚ)/2500000000),((1424940833:ℚ)/2000000000),((1896129643:ℚ)/3634375000),((13848467497:ℚ)/23070000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((61196021:ℚ)/156250000),((-32737511332206966150357037579932850016881898536771:ℚ)/12001325584411621093750000000000000000000000000000000),((-123919289925461722001403133:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/2),((9:ℚ)/16),((1770983317:ℚ)/2500000000),((7184111963:ℚ)/10000000000),((1910983317:ℚ)/3664062500),((69777007667:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((370637897:ℚ)/1000000000),((-30317199205457866890325161741489722994513077688423:ℚ)/10980208963155746459960937500000000000000000000000000),((-124094038694360664948098813:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((7143347321:ℚ)/10000000000),((1448703847:ℚ)/2000000000),((7703347321:ℚ)/14775000000),((14062334623:ℚ)/23450000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((217761031:ℚ)/625000000),((-521252882142844084316507755513346823554555074531971:ℚ)/186654614257812500000000000000000000000000000000000000),((-1988308677795493481225498197:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((1440552149:ℚ)/2000000000),((7302925991:ℚ)/10000000000),((1552552149:ℚ)/2978750000),((70846333919:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3247463867:ℚ)/10000000000),((-466240363954925364940634318240809953535898083704117:ℚ)/165189402917480468750000000000000000000000000000000000),((-79644832610595703758657917:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1452434711:ℚ)/2000000000),((1840583061:ℚ)/2500000000),((1564434711:ℚ)/3002500000),((17845247549:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((11690607:ℚ)/39062500),((-30140981146704568300077351516453431920288883715983:ℚ)/10573264166259765625000000000000000000000000000000000),((-79757641278939449468978357:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((7321585767:ℚ)/10000000000),((3710869003:ℚ)/5000000000),((7881585767:ℚ)/15131250000),((35957821027:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2715118087:ℚ)/10000000000),((-2307421559890110163986837725925250170041897089736237:ℚ)/801937779235839843750000000000000000000000000000000000),((-1996769328432656571693547413:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((1476199479:ℚ)/2000000000),((7481143289:ℚ)/10000000000),((1588199479:ℚ)/3050000000),((72450289601:ℚ)/121050000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1203237313:ℚ)/5000000000),((-514676855915127071769658415711741752351730149022047:ℚ)/177328906250000000000000000000000000000000000000000000),((-79984228202676151747802997:ℚ)/591462400000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((7440408451:ℚ)/10000000000),((7599952461:ℚ)/10000000000),((380971831:ℚ)/737500000),((73519572149:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1026469547:ℚ)/5000000000),((-1665306946658953456682551803147854979122758377703:ℚ)/626766967773437500000000000000000000000000000000000),((-2002450162212481221089778317:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((944903613:ℚ)/1250000000),((1929689961:ℚ)/2500000000),((1014903613:ℚ)/1965625000),((18647209649:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((32383871:ℚ)/312500000),((-125364008290838769270258245709195068339080044229:ℚ)/46353449858725070953369140625000000000000000000000),((-31377551872646445781410573:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((3839023613:ℚ)/5000000000),((7956369559:ℚ)/10000000000),((1373007871:ℚ)/2700000000),((76727326031:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-3408448590527113711078731027601423160245750091207:ℚ)/1518750000000000000000000000000000000000000000000000),((-139205759:ℚ)/1024000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((7915677857:ℚ)/10000000000),((985705957:ℚ)/1000000000),((8475677857:ℚ)/20000000000),((9383353613:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2203711609455520277338287984577043:ℚ)/750000000000000000000000000000000000),((-139205759:ℚ)/1024000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((1963299877:ℚ)/2000000000),((13657869403:ℚ)/10000000000),((2075299877:ℚ)/5520000000),((128040824627:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((58217614810926334716131:ℚ)/7617600000000000000000000),((-139205759:ℚ)/1024000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC25
#check @N11Formalization.C450NinthGroupedC25.bound
#print axioms N11Formalization.C450NinthGroupedC25.valid0
#print axioms N11Formalization.C450NinthGroupedC25.valid1
#print axioms N11Formalization.C450NinthGroupedC25.valid2
#print axioms N11Formalization.C450NinthGroupedC25.valid3
#print axioms N11Formalization.C450NinthGroupedC25.valid4
#print axioms N11Formalization.C450NinthGroupedC25.valid5
#print axioms N11Formalization.C450NinthGroupedC25.valid6
#print axioms N11Formalization.C450NinthGroupedC25.valid7
#print axioms N11Formalization.C450NinthGroupedC25.valid8
#print axioms N11Formalization.C450NinthGroupedC25.valid9
#print axioms N11Formalization.C450NinthGroupedC25.valid10
#print axioms N11Formalization.C450NinthGroupedC25.valid11
#print axioms N11Formalization.C450NinthGroupedC25.valid12
#print axioms N11Formalization.C450NinthGroupedC25.valid13
#print axioms N11Formalization.C450NinthGroupedC25.valid14
#print axioms N11Formalization.C450NinthGroupedC25.valid15
#print axioms N11Formalization.C450NinthGroupedC25.valid16
#print axioms N11Formalization.C450NinthGroupedC25.bound
#print axioms N11Formalization.C450NinthGroupedC25.endpoint_checks
