import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/4),((13:ℚ)/16),((5185407857:ℚ)/10000000000),((2760806091:ℚ)/5000000000),((20196223571:ℚ)/25750000000),((45490479183:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((819905213:ℚ)/1000000000),((-68366593792146584545975412345340285312185447:ℚ)/202273740160000000000000000000000000000000000),((-27638311202504640344246589:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((5424377409:ℚ)/10000000000),((5760755993:ℚ)/10000000000),((20913132227:ℚ)/26700000000),((94089827909:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((969976963:ℚ)/1250000000),((-71724819751157235774920107611226041172180026428979417506983:ℚ)/211315687670898437500000000000000000000000000000000000000000),((-108813004359657902027826181:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((2831620741:ℚ)/5000000000),((1470071093:ℚ)/2500000000),((10814862223:ℚ)/13587500000),((23910924209:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1825041423:ℚ)/2500000000),((-1836176444130315907103099544145025387532961625274110947342569:ℚ)/5206059477256250000000000000000000000000000000000000000000000),((-6745488846071398245374581:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((5782637459:ℚ)/10000000000),((749973219:ℚ)/1250000000),((21987912377:ℚ)/27650000000),((12149651847:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((35306919:ℚ)/50000000),((-15107094446116910418353249225183974870707582282523483054187:ℚ)/42808590491913604736328125000000000000000000000000000000000),((-1672384245756661015896009:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((5902011067:ℚ)/10000000000),((76490769:ℚ)/125000000),((22346033201:ℚ)/28125000000),((1234379997:ℚ)/1382500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6815765909:ℚ)/10000000000),((-118998661962243256328115228327891594312782341743319:ℚ)/337038378906250000000000000000000000000000000000000),((-16582392392049382663359:ℚ)/36100000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((120427269:ℚ)/200000000),((3089495103:ℚ)/5000000000),((454081807:ℚ)/567250000),((16587812113:ℚ)/18750000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6562519591:ℚ)/10000000000),((-2818940546381683792769067609363853000682816084353481476639177:ℚ)/7855775451660156250000000000000000000000000000000000000000000),((-26417725265959020008902821:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((6081032019:ℚ)/10000000000),((3119356483:ℚ)/5000000000),((22883096057:ℚ)/28600000000),((50151634279:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6432747549:ℚ)/10000000000),((-334836061589775952920787536814706314853158203572999878017917:ℚ)/933115916202894531250000000000000000000000000000000000000000),((-72861479865119474888581:ℚ)/160000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6140695677:ℚ)/10000000000),((1574607487:ℚ)/2500000000),((23062087031:ℚ)/28837500000),((25269897331:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3150349941:ℚ)/5000000000),((-23269385800339804074236619959376274835148667982565377843004499:ℚ)/64847324089762500000000000000000000000000000000000000000000000),((-6546908656768244242644461:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3100177273:ℚ)/5000000000),((397383831:ℚ)/625000000),((11620531819:ℚ)/14537500000),((2121996601:ℚ)/2403125000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1233245459:ℚ)/2000000000),((-1683892387986619647503716623631405090587072911857817697587:ℚ)/4692761931446235656738281250000000000000000000000000000000),((-407369474350504047454659:ℚ)/902500000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((782501093:ℚ)/1250000000),((1604461787:ℚ)/2500000000),((2927503279:ℚ)/3664062500),((25658003231:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((753645551:ℚ)/1250000000),((-3031102370774760455061785711609553644022871021382385189329077:ℚ)/8447435445992846679687500000000000000000000000000000000000000),((-6488757334032383459680261:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6319658387:ℚ)/10000000000),((3238773819:ℚ)/5000000000),((23598975161:ℚ)/29550000000),((51704059647:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((588932721:ℚ)/1000000000),((-1878828257985304969344079188656730000838256598940793588136881:ℚ)/5236296863552856445312500000000000000000000000000000000000000),((-25837783472857388667791709:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1275860717:ℚ)/2000000000),((1307448579:ℚ)/2000000000),((4755582151:ℚ)/5957500000),((6945610509:ℚ)/7880000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((179578437:ℚ)/312500000),((-6230947363499267868001205199853081331615854343881014048217943:ℚ)/17366278222398800000000000000000000000000000000000000000000000),((-4115185389672462753056829:ℚ)/9241600000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1287788889:ℚ)/2000000000),((1319386609:ℚ)/2000000000),((4791366667:ℚ)/6005000000),((20992025917:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((224019261:ℚ)/400000000),((-2735568636604203736206526815941326270336349839700636658480119:ℚ)/7624619518642455859375000000000000000000000000000000000000000),((-4096224782589630115799989:ℚ)/9241600000000000000000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((6498581071:ℚ)/10000000000),((6716298507:ℚ)/10000000000),((24135743213:ℚ)/30500000000),((106511880591:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1362745121:ℚ)/2500000000),((-14247207889399053182849247648880424949405147217226933527711213:ℚ)/40287350745756250000000000000000000000000000000000000000000000),((-101450039865360719094323181:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6617842021:ℚ)/10000000000),((136712899:ℚ)/200000000),((24493526063:ℚ)/30975000000),((2161267687:ℚ)/2440000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((5140328163:ℚ)/10000000000),((-4108249291213050380397014074559608883373323359127516553863:ℚ)/11614776656700000000000000000000000000000000000000000000000),((-40193756954215787341069:ℚ)/92416000000000000000000)⟩
theorem valid14 : Valid source31 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6737087203:ℚ)/10000000000),((1390994649:ℚ)/2000000000),((24851261609:ℚ)/31450000000),((7307643479:ℚ)/8260000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4811596109:ℚ)/10000000000),((-68776616696485034924459730995212787877486225235518619259:ℚ)/194412172559130859375000000000000000000000000000000000000),((-3980346994065497727672069:ℚ)/9241600000000000000000000)⟩
theorem valid15 : Valid source31 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source31 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((857039667:ℚ)/1250000000),((7193578613:ℚ)/10000000000),((3151119001:ℚ)/4050000000),((112716521969:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4460758899:ℚ)/10000000000),((-9366886574408150162486136789184616294506306687349928759025241:ℚ)/27212642967150000000000000000000000000000000000000000000000000),((-97527021230471012169442861:ℚ)/231040000000000000000000000)⟩
theorem valid16 : Valid source31 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source31 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7094735123:ℚ)/10000000000),((4550260777:ℚ)/5000000000),((25924205369:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1833469579:ℚ)/5000000000),((-483776831393302605078909226853932579:ℚ)/2000000000000000000000000000000000000),((-52109467:ℚ)/128000000)⟩
theorem valid17 : Valid source31 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((4500250619:ℚ)/5000000000),((12908653783:ℚ)/10000000000),((15820751857:ℚ)/27600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-24728086598281604945988347:ℚ)/126960000000000000000000000),((-52109467:ℚ)/128000000)⟩
theorem valid18 : Valid source31 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source31 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source31 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC29
#check @N11Formalization.C450Source31GroupedC29.bound
#print axioms N11Formalization.C450Source31GroupedC29.valid0
#print axioms N11Formalization.C450Source31GroupedC29.valid1
#print axioms N11Formalization.C450Source31GroupedC29.valid2
#print axioms N11Formalization.C450Source31GroupedC29.valid3
#print axioms N11Formalization.C450Source31GroupedC29.valid4
#print axioms N11Formalization.C450Source31GroupedC29.valid5
#print axioms N11Formalization.C450Source31GroupedC29.valid6
#print axioms N11Formalization.C450Source31GroupedC29.valid7
#print axioms N11Formalization.C450Source31GroupedC29.valid8
#print axioms N11Formalization.C450Source31GroupedC29.valid9
#print axioms N11Formalization.C450Source31GroupedC29.valid10
#print axioms N11Formalization.C450Source31GroupedC29.valid11
#print axioms N11Formalization.C450Source31GroupedC29.valid12
#print axioms N11Formalization.C450Source31GroupedC29.valid13
#print axioms N11Formalization.C450Source31GroupedC29.valid14
#print axioms N11Formalization.C450Source31GroupedC29.valid15
#print axioms N11Formalization.C450Source31GroupedC29.valid16
#print axioms N11Formalization.C450Source31GroupedC29.valid17
#print axioms N11Formalization.C450Source31GroupedC29.valid18
#print axioms N11Formalization.C450Source31GroupedC29.bound
#print axioms N11Formalization.C450Source31GroupedC29.endpoint_checks
