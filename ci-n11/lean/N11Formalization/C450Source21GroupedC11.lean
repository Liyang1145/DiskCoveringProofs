import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((1598831199:ℚ)/2500000000),((669463887:ℚ)/1000000000),((-1400391661:ℚ)/4960000000),((-958831199:ℚ)/5150000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2853804693:ℚ)/5000000000),((3009124798619215407690224909659622148082297798433011961:ℚ)/26464482031250000000000000000000000000000000000000000000),((23029645718251883587550087:ℚ)/554496000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((1658597711:ℚ)/2500000000),((693367357:ℚ)/1000000000),((-1472102071:ℚ)/5150000000),((-1018597711:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((31849173:ℚ)/62500000),((307405944757717752265336863737651896661384410982032553:ℚ)/2722942762500000000000000000000000000000000000000000000),((6237478104822506945077709:ℚ)/184832000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((859168053:ℚ)/1250000000),((7053150309:ℚ)/10000000000),((-15079450927:ℚ)/53400000000),((-539168053:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2204271839:ℚ)/5000000000),((3694347265677091577079403417581483573924949315853815151:ℚ)/33488827080175781250000000000000000000000000000000000000),((3592208160270044582749583:ℚ)/138624000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((437048923:ℚ)/625000000),((7112879149:ℚ)/10000000000),((-15258637447:ℚ)/54350000000),((-92349641:ℚ)/456875000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((251533101:ℚ)/625000000),((17673163013768109441921311789707358063358528015265543:ℚ)/161972674376296997070312500000000000000000000000000000),((253897494901448985226341:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7052492919:ℚ)/10000000000),((7172601857:ℚ)/10000000000),((-15437805571:ℚ)/54825000000),((-4492492919:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3818962873:ℚ)/10000000000),((252644749353363274116382440283848603936816998769640547167:ℚ)/2317896517256250000000000000000000000000000000000000000000),((177499303649675156385775607:ℚ)/8871936000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((444512329:ℚ)/625000000),((7232318591:ℚ)/10000000000),((-15616955773:ℚ)/55300000000),((-284512329:ℚ)/1394375000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3602309829:ℚ)/10000000000),((63767805600820903525450862999876752582106530408707217:ℚ)/585630826208400726318359375000000000000000000000000000),((208305532115772382366589:ℚ)/11552000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((7171895953:ℚ)/10000000000),((1458405901:ℚ)/2000000000),((-3159217703:ℚ)/11155000000),((-1537298651:ℚ)/7500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((674485911:ℚ)/2000000000),((2499650212345509034092262794608279098365519464081228429:ℚ)/22978591918945312500000000000000000000000000000000000000),((47477091761563601780344461:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((7231589131:ℚ)/10000000000),((7411434457:ℚ)/10000000000),((-16154303371:ℚ)/56250000000),((-424689921:ℚ)/2080000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1563200191:ℚ)/5000000000),((55463699063403899962388758372412255829738279754144561:ℚ)/506188800000000000000000000000000000000000000000000000),((41619049616973235888395269:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((7350959511:ℚ)/10000000000),((7530817837:ℚ)/10000000000),((-16512453511:ℚ)/57200000000),((-4790959511:ℚ)/23260000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((102682467:ℚ)/400000000),((1229983911655108396903791218469416785967175446843186010673:ℚ)/11247219891050000000000000000000000000000000000000000000000),((89628503607108057145718327:ℚ)/8871936000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((3735154733:ℚ)/5000000000),((3825090349:ℚ)/5000000000),((-8435271047:ℚ)/29075000000),((-818384911:ℚ)/3940000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((925021599:ℚ)/5000000000),((12132828069940808724566490120122930293641412276466802677:ℚ)/111144609987500000000000000000000000000000000000000000000),((4524371605735977139481781:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((948704999:ℚ)/1250000000),((7888848729:ℚ)/10000000000),((-17586546187:ℚ)/59100000000),((-628704999:ℚ)/3050000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((130550219:ℚ)/2500000000),((11592004027278200515001303371366814831264580441144902441:ℚ)/104801383593750000000000000000000000000000000000000000000),((98170717494963169449629:ℚ)/46208000000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((391412321:ℚ)/500000000),((1673195587:ℚ)/2000000000),((-3803586761:ℚ)/12200000000),((-87804107:ℚ)/432000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((386684708989028493662297084047214155524932559828223:ℚ)/3415219200000000000000000000000000000000000000000000),((1819747:ℚ)/1024000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((2076315849:ℚ)/2500000000),((5136231043:ℚ)/5000000000),((-12368693129:ℚ)/32400000000),((-1436315849:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((32974286950416656123556679310646358865180458801285489201:ℚ)/259200000000000000000000000000000000000000000000000000000),((1819747:ℚ)/1024000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((5105703133:ℚ)/5000000000),((7040029029:ℚ)/5000000000),((-18080087087:ℚ)/40000000000),((-3825703133:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2437612903854160976826293673626217034957389431122236613:ℚ)/16819660800000000000000000000000000000000000000000000000),((1819747:ℚ)/1024000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC11
#check @N11Formalization.C450Source21GroupedC11.bound
#print axioms N11Formalization.C450Source21GroupedC11.valid0
#print axioms N11Formalization.C450Source21GroupedC11.valid1
#print axioms N11Formalization.C450Source21GroupedC11.valid2
#print axioms N11Formalization.C450Source21GroupedC11.valid3
#print axioms N11Formalization.C450Source21GroupedC11.valid4
#print axioms N11Formalization.C450Source21GroupedC11.valid5
#print axioms N11Formalization.C450Source21GroupedC11.valid6
#print axioms N11Formalization.C450Source21GroupedC11.valid7
#print axioms N11Formalization.C450Source21GroupedC11.valid8
#print axioms N11Formalization.C450Source21GroupedC11.valid9
#print axioms N11Formalization.C450Source21GroupedC11.valid10
#print axioms N11Formalization.C450Source21GroupedC11.valid11
#print axioms N11Formalization.C450Source21GroupedC11.valid12
#print axioms N11Formalization.C450Source21GroupedC11.valid13
#print axioms N11Formalization.C450Source21GroupedC11.bound
#print axioms N11Formalization.C450Source21GroupedC11.endpoint_checks
