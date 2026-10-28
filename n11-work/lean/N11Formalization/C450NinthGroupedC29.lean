import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((593719291:ℚ)/1000000000),((6462430219:ℚ)/10000000000),((1893157873:ℚ)/2670000000),((89131592847:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3370976179:ℚ)/5000000000),((-41774321993036349715126585949490263:ℚ)/2379270375000000000000000000000000000),((-24220305450975854945107977:ℚ)/147865600000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6412392747:ℚ)/10000000000),((418751159:ℚ)/625000000),((20357178241:ℚ)/27650000000),((5763765067:ℚ)/6675000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((566590623:ℚ)/1000000000),((-8154382854647898337370622622029191891027504695637493059:ℚ)/396357133593750000000000000000000000000000000000000000000),((-7252958765767382460724987259:ℚ)/44359680000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((166249559:ℚ)/250000000),((1704702617:ℚ)/2500000000),((526748677:ℚ)/703125000),((23441134021:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5053653049:ℚ)/10000000000),((-15927781150528486784846159277476584029777314779687:ℚ)/724196434020996093750000000000000000000000000000000),((-1509701463392176260408577:ℚ)/9241600000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((1353754979:ℚ)/2000000000),((6937600999:ℚ)/10000000000),((4285264937:ℚ)/5720000000),((31769604329:ℚ)/37500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4720713823:ℚ)/10000000000),((-2342247081436696936877756040475656910049287231527411:ℚ)/106334800000000000000000000000000000000000000000000000),((-96514917165668924131523897:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6887566017:ℚ)/10000000000),((6996995763:ℚ)/10000000000),((21782698051:ℚ)/28837500000),((96080944919:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4364484807:ℚ)/10000000000),((-2551908098106140975555443880319698285121403270378245089:ℚ)/112412369778442382812500000000000000000000000000000000000),((-7235495726654680734706275539:ℚ)/44359680000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6946961069:ℚ)/10000000000),((1764097551:ℚ)/2500000000),((21960883207:ℚ)/29075000000),((24213268163:ℚ)/28837500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1043945199:ℚ)/2500000000),((-139539303408145764777524796652997545042334737202085079:ℚ)/6144678699218750000000000000000000000000000000000000000),((-2410515708128818873891301337:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((3503177897:ℚ)/5000000000),((711578433:ℚ)/1000000000),((11069533691:ℚ)/14656250000),((9762519629:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3978685673:ℚ)/10000000000),((-47890265638827200345760796313901032736254933934947023:ℚ)/2108200120925903320312500000000000000000000000000000000),((-602300484905477385864957953:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((7065750199:ℚ)/10000000000),((7175178149:ℚ)/10000000000),((22317250597:ℚ)/29550000000),((98397315937:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1885940237:ℚ)/5000000000),((-33930793702247835945805539267061857407634589172925503:ℚ)/1493236914062500000000000000000000000000000000000000000),((-2407890603142783410044023617:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1781286073:ℚ)/2500000000),((7234571667:ℚ)/10000000000),((5623858219:ℚ)/7446875000),((99169431671:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((888416597:ℚ)/2500000000),((-175999221011205476664066121424841056819932036716745841:ℚ)/7743253261756896972656250000000000000000000000000000000),((-150411356158120775744764193:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((44903363:ℚ)/62500000),((1823491223:ℚ)/2500000000),((141710089:ℚ)/187656250),((24985385899:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3321791551:ℚ)/10000000000),((-29344095266559425291056287107775876632030510171:ℚ)/1290681660920381546020507812500000000000000000000),((-93956063498608748913673:ℚ)/577600000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((7243931571:ℚ)/10000000000),((7353357831:ℚ)/10000000000),((22851794713:ℚ)/30262500000),((100713651803:ℚ)/120100000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3073160833:ℚ)/10000000000),((-437683674670795702134181411922246971761531047889262009:ℚ)/19246506701660156250000000000000000000000000000000000000),((-7211913552180615768372809291:ℚ)/44359680000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((1825831193:ℚ)/2500000000),((741275049:ℚ)/1000000000),((5757493579:ℚ)/7625000000),((10148575637:ℚ)/12105000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1401657281:ℚ)/5000000000),((-63024237393381219395029924261696002461804691972735947:ℚ)/2770764160156250000000000000000000000000000000000000000),((-150166848365916577477444833:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((7362717689:ℚ)/10000000000),((1882883749:ℚ)/2500000000),((23208153067:ℚ)/30975000000),((25757488737:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((313175197:ℚ)/1250000000),((-342961952939584773312759126213685631625242010655255793:ℚ)/15478637036132812500000000000000000000000000000000000000),((-2399771795977141553844010657:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3740751349:ℚ)/5000000000),((382515923:ℚ)/500000000),((11782254047:ℚ)/15725000000),((1742902333:ℚ)/2065000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((442046897:ℚ)/2500000000),((-526319583243877542629221450432290972912590264147311:ℚ)/23732966327667236328125000000000000000000000000000000),((-599633779081245380363367017:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((7600286649:ℚ)/10000000000),((3943941221:ℚ)/5000000000),((23920859947:ℚ)/32400000000),((53831235873:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-166058024326520397369887114807364714566853378495899953:ℚ)/7873200000000000000000000000000000000000000000000000000),((-166146083:ℚ)/1024000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((1959462891:ℚ)/2500000000),((1957656971:ℚ)/2000000000),((6158388673:ℚ)/10000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-11917483622922715638606782008294908625387317755157467:ℚ)/1171875000000000000000000000000000000000000000000000000),((-166146083:ℚ)/1024000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((4869129923:ℚ)/5000000000),((13588757193:ℚ)/10000000000),((15167389769:ℚ)/27600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-19003250117767656614129077861855499:ℚ)/5256144000000000000000000000000000000),((-166146083:ℚ)/1024000000)⟩
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
end N11Formalization.C450NinthGroupedC29
#check @N11Formalization.C450NinthGroupedC29.bound
#print axioms N11Formalization.C450NinthGroupedC29.valid0
#print axioms N11Formalization.C450NinthGroupedC29.valid1
#print axioms N11Formalization.C450NinthGroupedC29.valid2
#print axioms N11Formalization.C450NinthGroupedC29.valid3
#print axioms N11Formalization.C450NinthGroupedC29.valid4
#print axioms N11Formalization.C450NinthGroupedC29.valid5
#print axioms N11Formalization.C450NinthGroupedC29.valid6
#print axioms N11Formalization.C450NinthGroupedC29.valid7
#print axioms N11Formalization.C450NinthGroupedC29.valid8
#print axioms N11Formalization.C450NinthGroupedC29.valid9
#print axioms N11Formalization.C450NinthGroupedC29.valid10
#print axioms N11Formalization.C450NinthGroupedC29.valid11
#print axioms N11Formalization.C450NinthGroupedC29.valid12
#print axioms N11Formalization.C450NinthGroupedC29.valid13
#print axioms N11Formalization.C450NinthGroupedC29.valid14
#print axioms N11Formalization.C450NinthGroupedC29.valid15
#print axioms N11Formalization.C450NinthGroupedC29.valid16
#print axioms N11Formalization.C450NinthGroupedC29.bound
#print axioms N11Formalization.C450NinthGroupedC29.endpoint_checks
