import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((391224283:ℚ)/625000000),((3261827097:ℚ)/5000000000),((-8985481291:ℚ)/24800000000),((-343224283:ℚ)/1287500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3015069709:ℚ)/5000000000),((7065984673158817195732859856660521696404899864664111:ℚ)/620261297607421875000000000000000000000000000000000000),((3140704461152046855584603:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((6497195989:ℚ)/10000000000),((6761291107:ℚ)/10000000000),((-18683873321:ℚ)/51500000000),((-5729195989:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1090898871:ℚ)/2000000000),((8889103989413593429686867360248272921022119744676756707:ℚ)/784207515600000000000000000000000000000000000000000000000),((12477585043391030365525283:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3367397899:ℚ)/5000000000),((6880105971:ℚ)/10000000000),((-19040317913:ℚ)/53400000000),((-2983397899:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1204526663:ℚ)/2500000000),((11871974791832992770737938023517341290409233000248532833:ℚ)/1071642466565625000000000000000000000000000000000000000000),((12377198377312710177982147:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((1713398271:ℚ)/2500000000),((1399783721:ℚ)/2000000000),((-3879351163:ℚ)/10870000000),((-1521398271:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4469060233:ℚ)/10000000000),((99279965343337523754870514070976225504774575338786633:ℚ)/8975837587841796875000000000000000000000000000000000000),((493411232944483897833147:ℚ)/9241600000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1394477749:ℚ)/2000000000),((7058324121:ℚ)/10000000000),((-19574972363:ℚ)/55300000000),((-1240877749:ℚ)/4462000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4092498749:ℚ)/10000000000),((105013470915635834671405886419175037137047770663843173:ℚ)/9594975456598437500000000000000000000000000000000000000),((12285333060878960950198747:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((7031785991:ℚ)/10000000000),((7117729121:ℚ)/10000000000),((-19753187363:ℚ)/55775000000),((-6263785991:ℚ)/22500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((121606811:ℚ)/312500000),((10179385152945690859717384368070440396208678181119688443:ℚ)/930632972717285156250000000000000000000000000000000000000),((12264548891035206495868747:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((3545591431:ℚ)/5000000000),((893428929:ℚ)/1250000000),((-2480286787:ℚ)/7031250000),((-3161591431:ℚ)/11297500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3679953713:ℚ)/10000000000),((441346861460297379225290246998256221870131080007197711:ℚ)/40554549474169921875000000000000000000000000000000000000),((191244318010657062146047:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((178022029:ℚ)/250000000),((3588566809:ℚ)/5000000000),((-9965700427:ℚ)/28243750000),((-158822029:ℚ)/567250000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((7139507:ℚ)/20000000),((70111139832050462866097695835522947697460998237419:ℚ)/6444005246773803710937500000000000000000000000000000),((3057321976900470617960027:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((3575289683:ℚ)/5000000000),((7206835683:ℚ)/10000000000),((-20020507049:ℚ)/56725000000),((-3191289683:ℚ)/11392500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3456196571:ℚ)/10000000000),((38014041282576779825922575440905923916534295058124612629:ℚ)/3494784288678662109375000000000000000000000000000000000000),((12218956900102365708716963:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((1795069371:ℚ)/2500000000),((3618268813:ℚ)/5000000000),((-10054806439:ℚ)/28481250000),((-1603069371:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1669469963:ℚ)/5000000000),((28982453929168476958785235508766223652479919960998822127:ℚ)/2665122259800000000000000000000000000000000000000000000000),((3052160831967170258637123:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-3:ℚ)/8),((-5:ℚ)/16),((7209975513:ℚ)/10000000000),((7266239449:ℚ)/10000000000),((-20198718347:ℚ)/57200000000),((-6441975513:ℚ)/22975000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((1608789289:ℚ)/5000000000),((58920550172764425965555093584657885738791755011953977399:ℚ)/5419417623876953125000000000000000000000000000000000000000),((12198347191462897277471067:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((452479591:ℚ)/625000000),((1459188231:ℚ)/2000000000),((-4057564693:ℚ)/11487500000),((-404479591:ℚ)/1441875000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3091628613:ℚ)/10000000000),((10965836762092694342741803735275045663758184634633:ℚ)/1008857107679575681686401367187500000000000000000000),((487522739585460220664987:ℚ)/9241600000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((454335707:ℚ)/625000000),((3677672109:ℚ)/5000000000),((-10233016327:ℚ)/28837500000),((-406335707:ℚ)/1453750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((296050387:ℚ)/1000000000),((241745407854994164733895206196651784640225506595328129:ℚ)/22149646498590087890625000000000000000000000000000000000),((3045527424488589383261827:ℚ)/57760000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((732876677:ℚ)/1000000000),((296589873:ℚ)/400000000),((-825769619:ℚ)/2326000000),((-656076677:ℚ)/2345000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((669915161:ℚ)/2500000000),((1533742008925159910863935030840468568458570940013802373:ℚ)/140598126055078125000000000000000000000000000000000000000),((19458678799822836124843:ℚ)/369664000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7388161897:ℚ)/10000000000),((7474148989:ℚ)/10000000000),((-2974635281:ℚ)/8375000000),((-6620161897:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((473319291:ℚ)/2000000000),((2513318345842753448958270667640858829114297662483883257:ℚ)/230507995950000000000000000000000000000000000000000000000),((12141308533379777198167907:ℚ)/231040000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((74475567:ℚ)/100000000),((3796476013:ℚ)/5000000000),((-10589428039:ℚ)/29550000000),((-66795567:ℚ)/240200000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2006277453:ℚ)/10000000000),((70310333946705977208860707678568193535141541040313:ℚ)/6398770301193750000000000000000000000000000000000000),((159603662895852167876817:ℚ)/3040000000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((3783172683:ℚ)/5000000000),((771175341:ℚ)/1000000000),((-2153526023:ℚ)/6005000000),((-3399172683:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((941436501:ℚ)/10000000000),((74803934687178922003662956188931576526492339106333137667:ℚ)/6815104525000000000000000000000000000000000000000000000000),((6354079413199347:ℚ)/121600000000000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((7685132827:ℚ)/10000000000),((818694387:ℚ)/1000000000),((-2296083161:ℚ)/6100000000),((-6917132827:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((12678235671113485000531550264024465466030963495005703901:ℚ)/1106531020800000000000000000000000000000000000000000000000),((1669843:ℚ)/32000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((4080135841:ℚ)/5000000000),((1260940587:ℚ)/1250000000),((-3582821761:ℚ)/8100000000),((-3696135841:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13445265780312217147715199872437314179835929628790005961:ℚ)/1036800000000000000000000000000000000000000000000000000000),((1669843:ℚ)/32000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10060695147:ℚ)/10000000000),((1736025801:ℚ)/1250000000),((-5008077403:ℚ)/10000000000),((-3097565049:ℚ)/14720000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((36645644437375703661856989491570991213444151745554809:ℚ)/2491801600000000000000000000000000000000000000000000000),((1669843:ℚ)/32000000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC11
#check @N11Formalization.C450SeventhGroupedC11.bound
#print axioms N11Formalization.C450SeventhGroupedC11.valid0
#print axioms N11Formalization.C450SeventhGroupedC11.valid1
#print axioms N11Formalization.C450SeventhGroupedC11.valid2
#print axioms N11Formalization.C450SeventhGroupedC11.valid3
#print axioms N11Formalization.C450SeventhGroupedC11.valid4
#print axioms N11Formalization.C450SeventhGroupedC11.valid5
#print axioms N11Formalization.C450SeventhGroupedC11.valid6
#print axioms N11Formalization.C450SeventhGroupedC11.valid7
#print axioms N11Formalization.C450SeventhGroupedC11.valid8
#print axioms N11Formalization.C450SeventhGroupedC11.valid9
#print axioms N11Formalization.C450SeventhGroupedC11.valid10
#print axioms N11Formalization.C450SeventhGroupedC11.valid11
#print axioms N11Formalization.C450SeventhGroupedC11.valid12
#print axioms N11Formalization.C450SeventhGroupedC11.valid13
#print axioms N11Formalization.C450SeventhGroupedC11.valid14
#print axioms N11Formalization.C450SeventhGroupedC11.valid15
#print axioms N11Formalization.C450SeventhGroupedC11.valid16
#print axioms N11Formalization.C450SeventhGroupedC11.valid17
#print axioms N11Formalization.C450SeventhGroupedC11.valid18
#print axioms N11Formalization.C450SeventhGroupedC11.valid19
#print axioms N11Formalization.C450SeventhGroupedC11.bound
#print axioms N11Formalization.C450SeventhGroupedC11.endpoint_checks
