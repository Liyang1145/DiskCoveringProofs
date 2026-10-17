import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((6004164927:ℚ)/10000000000),((6522370271:ℚ)/10000000000),((2129388309:ℚ)/3560000000),((76226072981:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3299759669:ℚ)/5000000000),((-67030603420446009375575769625249:ℚ)/11279504000000000000000000000000000),((-5827567426485858907894062481:ℚ)/44359680000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6479402369:ℚ)/10000000000),((6759960657:ℚ)/10000000000),((86878511:ℚ)/140000000),((78839567227:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2749728113:ℚ)/5000000000),((-386741624467423267676082106779562211898556535179:ℚ)/51450000000000000000000000000000000000000000000000),((-1947278829977278585713342043:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((1679252211:ℚ)/2500000000),((6878753559:ℚ)/10000000000),((591750737:ℚ)/937500000),((80146289149:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4868371691:ℚ)/10000000000),((-14145848208999315642399793820137045626345202363957:ℚ)/1716613769531250000000000000000000000000000000000000),((-365577771707263121778810169:ℚ)/2772480000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6835809383:ℚ)/10000000000),((1749386259:ℚ)/2500000000),((7219809383:ℚ)/11440000000),((20363248849:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4522901561:ℚ)/10000000000),((-7047844854766932234239131242638737659904761487076699:ℚ)/850678400000000000000000000000000000000000000000000000),((-1951005536930494014816702507:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((6954608241:ℚ)/10000000000),((7056940261:ℚ)/10000000000),((2446202747:ℚ)/3845000000),((82106342871:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4150899953:ℚ)/10000000000),((-2297702215748456330143143092407929637968283999594687:ℚ)/266458950585937500000000000000000000000000000000000000),((-5856834431840790131807233009:ℚ)/44359680000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7014007067:ℚ)/10000000000),((1779083789:ℚ)/2500000000),((7398007067:ℚ)/11630000000),((20689921679:ℚ)/28837500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3952621203:ℚ)/10000000000),((-3397399442927026166844295190406021924166135404028069:ℚ)/393259436750000000000000000000000000000000000000000000),((-1952920142246970276827535907:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((7073405503:ℚ)/10000000000),((112120777:ℚ)/156250000),((7457405503:ℚ)/11725000000),((1303328547:ℚ)/1817187500),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3744436591:ℚ)/10000000000),((-1334484537821931797734349770469659911078739689993803:ℚ)/154199780273437500000000000000000000000000000000000000),((-1953565937102850174965576667:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((7132803559:ℚ)/10000000000),((3617561993:ℚ)/5000000000),((7516803559:ℚ)/11820000000),((42033181923:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1762293609:ℚ)/5000000000),((-2485316348265120986629139117149619196412549633020497:ℚ)/286701487500000000000000000000000000000000000000000000),((-1954215528549386684470972203:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((1798050311:ℚ)/2500000000),((455907371:ℚ)/625000000),((1894050311:ℚ)/2978750000),((5294981081:ℚ)/7387500000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1645365867:ℚ)/5000000000),((-4302669171329857342411077731990591215105699134123499:ℚ)/495568208752441406250000000000000000000000000000000000),((-122179307288307780607433323:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7251598567:ℚ)/10000000000),((7353911587:ℚ)/10000000000),((7635598567:ℚ)/12010000000),((85373027457:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((759908649:ℚ)/2500000000),((-5883942108398800598207473608981137999552139944136489:ℚ)/676688906640625000000000000000000000000000000000000000),((-1955526101322112248770628907:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((7310995537:ℚ)/10000000000),((463331559:ℚ)/625000000),((7694995537:ℚ)/12105000000),((5376647149:ℚ)/7506250000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((43228129:ℚ)/156250000),((-10725540865602468925227812157359537752353523795353911:ℚ)/1231776428906250000000000000000000000000000000000000000),((-1956187082707902557839788347:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((3685196081:ℚ)/5000000000),((233521813:ℚ)/312500000),((3877196081:ℚ)/6100000000),((2708739943:ℚ)/3782812500),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2464342441:ℚ)/10000000000),((-12368842320757472181857727052313266063611588497581503:ℚ)/1418631250000000000000000000000000000000000000000000000),((-489212965198081934421125243:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((148595769:ℚ)/200000000),((7591483327:ℚ)/10000000000),((52091923:ℚ)/82600000),((87986316597:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2120394221:ℚ)/10000000000),((-7444371157168625434496156610201032599917046781:ℚ)/880562462500000000000000000000000000000000000000),((-2349024522719361645524929:ℚ)/17743872000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3774290023:ℚ)/5000000000),((7710267571:ℚ)/10000000000),((3966290023:ℚ)/6290000000),((29764314427:ℚ)/41300000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((581954747:ℚ)/5000000000),((-12878259182206251130015667595798436899802842891649:ℚ)/1518909844970703125000000000000000000000000000000000),((-489717243869259583356688427:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((479210649:ℚ)/625000000),((3973916523:ℚ)/5000000000),((167736883:ℚ)/270000000),((45953081753:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-36387124212326549991134874054716474878998145247:ℚ)/4556250000000000000000000000000000000000000000000),((-135696497:ℚ)/1024000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((988118439:ℚ)/1250000000),((615515303:ℚ)/625000000),((1036118439:ℚ)/2000000000),((7050668333:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-8851551886770399709734486619140214265204425253433:ℚ)/3125000000000000000000000000000000000000000000000000),((-135696497:ℚ)/1024000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((2451358149:ℚ)/2500000000),((2729745641:ℚ)/2000000000),((849119383:ℚ)/1840000000),((30923202051:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1317355437534671307291:ℚ)/1692800000000000000000000),((-135696497:ℚ)/1024000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC27
#check @N11Formalization.C450EighthGroupedC27.bound
#print axioms N11Formalization.C450EighthGroupedC27.valid0
#print axioms N11Formalization.C450EighthGroupedC27.valid1
#print axioms N11Formalization.C450EighthGroupedC27.valid2
#print axioms N11Formalization.C450EighthGroupedC27.valid3
#print axioms N11Formalization.C450EighthGroupedC27.valid4
#print axioms N11Formalization.C450EighthGroupedC27.valid5
#print axioms N11Formalization.C450EighthGroupedC27.valid6
#print axioms N11Formalization.C450EighthGroupedC27.valid7
#print axioms N11Formalization.C450EighthGroupedC27.valid8
#print axioms N11Formalization.C450EighthGroupedC27.valid9
#print axioms N11Formalization.C450EighthGroupedC27.valid10
#print axioms N11Formalization.C450EighthGroupedC27.valid11
#print axioms N11Formalization.C450EighthGroupedC27.valid12
#print axioms N11Formalization.C450EighthGroupedC27.valid13
#print axioms N11Formalization.C450EighthGroupedC27.valid14
#print axioms N11Formalization.C450EighthGroupedC27.valid15
#print axioms N11Formalization.C450EighthGroupedC27.valid16
#print axioms N11Formalization.C450EighthGroupedC27.bound
#print axioms N11Formalization.C450EighthGroupedC27.endpoint_checks
