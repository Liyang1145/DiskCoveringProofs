import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((11:ℚ)/16),((3:ℚ)/4),((5181921521:ℚ)/10000000000),((2760855369:ℚ)/5000000000),((76841136731:ℚ)/103000000000),((349760197:ℚ)/400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8205324953:ℚ)/10000000000),((-56664442311511443005167635293241:ℚ)/164800000000000000000000000000000),((-1817634931033360028893791901:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5421583363:ℚ)/10000000000),((720185471:ℚ)/1250000000),((26492472331:ℚ)/35600000000),((2800556413:ℚ)/3218750000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((388253157:ℚ)/500000000),((-2502132864372926316710998129978526043646256786571669:ℚ)/7245891019701957702636718750000000000000000000000000),((-111916520104276717723968781:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((5661089409:ℚ)/10000000000),((5881309869:ℚ)/10000000000),((82111983499:ℚ)/108700000000),((22763929607:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7304410827:ℚ)/10000000000),((-1546519428424557486078483818144307806951888494908826511371:ℚ)/4310444829375000000000000000000000000000000000000000000000),((-7107321790094407448563602901:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((5780789199:ℚ)/10000000000),((600109851:ℚ)/1000000000),((11918383027:ℚ)/15800000000),((2312329553:ℚ)/2717500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3532565367:ℚ)/5000000000),((-16672417226872741629026915180735629162760716139473133:ℚ)/46446933625946044921875000000000000000000000000000000),((-195320130606690832024381:ℚ)/409600000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((5900455977:ℚ)/10000000000),((3060425811:ℚ)/5000000000),((84745015747:ℚ)/112500000000),((11741277433:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6819013057:ℚ)/10000000000),((-2978511802026945619893479835174028316799963195390727:ℚ)/8294303855895996093750000000000000000000000000000000),((-1748465504846997706829563861:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6020091441:ℚ)/10000000000),((3090357711:ℚ)/5000000000),((86061005851:ℚ)/113450000000),((11831073133:ℚ)/14062500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1313052437:ℚ)/2000000000),((-3597900345978658804349436869942955600818902598749640561:ℚ)/9859210252761840820312500000000000000000000000000000000),((-1741229012931700741133127661:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6079897929:ℚ)/10000000000),((1248114201:ℚ)/2000000000),((6670682863:ℚ)/8800000000),((4768342603:ℚ)/5672500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6435234927:ℚ)/10000000000),((-457914955125231367808251475894640495970372980398967921:ℚ)/1254862716787109375000000000000000000000000000000000000),((-277429506587151127332535741:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3069848587:ℚ)/5000000000),((3150209289:ℚ)/5000000000),((43688334457:ℚ)/57675000000),((12010627867:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6302929373:ℚ)/10000000000),((-60098445642544073961475506009038780250430746443286257:ℚ)/164700819067382812500000000000000000000000000000000000),((-1726581713364760737690693661:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6199489357:ℚ)/10000000000),((3180129169:ℚ)/5000000000),((88034382927:ℚ)/116300000000),((12100387507:ℚ)/14418750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6168195619:ℚ)/10000000000),((-265011818770341646229553812766103824725279439619227785491:ℚ)/726308811401824951171875000000000000000000000000000000000),((-1719170903743471636322192301:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((3129637327:ℚ)/5000000000),((6420090481:ℚ)/10000000000),((6335144371:ℚ)/8375000000),((24380271443:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((6030867597:ℚ)/10000000000),((-1126557859579758880601620403115561986678598644201707543379:ℚ)/3087701046357421875000000000000000000000000000000000000000),((-18966226990325573665802341:ℚ)/40960000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((3159526617:ℚ)/5000000000),((6479915191:ℚ)/10000000000),((44674792787:ℚ)/59100000000),((24559745573:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1472690131:ℚ)/2500000000),((-121215676502489859078955246879950251509984059634135316893:ℚ)/332252339057922363281250000000000000000000000000000000000),((-6816699836300576606783461021:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6378825261:ℚ)/10000000000),((130794653:ℚ)/200000000),((90007077871:ℚ)/119150000000),((494783959:ℚ)/591000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5747667793:ℚ)/10000000000),((-336472369358255663136192969838151156446670618689949587:ℚ)/922333020361875000000000000000000000000000000000000000),((-2714543715478334723628469:ℚ)/5914624000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1287718179:ℚ)/2000000000),((824942879:ℚ)/1250000000),((18132899969:ℚ)/24020000000),((3114828637:ℚ)/3723437500),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5601357167:ℚ)/10000000000),((-10601021532070411732026141093142453678447377335515625707:ℚ)/29061397398031353950500488281250000000000000000000000000),((-105559160894648933709797581:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((406146893:ℚ)/625000000),((1679785809:ℚ)/2500000000),((5707615823:ℚ)/7625000000),((6319357427:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1362891527:ℚ)/2500000000),((-17393595114721651040555638116518306631098763413087043557:ℚ)/48372683560638427734375000000000000000000000000000000000),((-418371435523795003920799021:ℚ)/924160000000000000000000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3308925473:ℚ)/5000000000),((1709679273:ℚ)/2500000000),((15439393401:ℚ)/20650000000),((6409037819:ℚ)/7625000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((5140304279:ℚ)/10000000000),((-5879116639559553781146057870901923217798233931674583777:ℚ)/16347508544921875000000000000000000000000000000000000000),((-414448113883551241737527389:ℚ)/924160000000000000000000000)⟩
theorem valid14 : Valid source33 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6737328369:ℚ)/10000000000),((695826581:ℚ)/1000000000),((93950612059:ℚ)/125800000000),((371354249:ℚ)/442500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2405455207:ℚ)/5000000000),((-155740977328116313933013877632179088434334422430909:ℚ)/432991867675781250000000000000000000000000000000000),((-65674668325816579049171301:ℚ)/147865600000000000000000000)⟩
theorem valid15 : Valid source33 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source33 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((6856783623:ℚ)/10000000000),((7197292313:ℚ)/10000000000),((95264619853:ℚ)/129600000000),((26711876939:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2229668293:ℚ)/5000000000),((-14899067789754517337056758303189790488084601227698019551:ℚ)/42562316953125000000000000000000000000000000000000000000),((-6437271226631791805004138429:ℚ)/14786560000000000000000000000)⟩
theorem valid16 : Valid source33 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((443476973:ℚ)/625000000),((9106875297:ℚ)/10000000000),((6118246703:ℚ)/10000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3663647843:ℚ)/10000000000),((-101034105607593181564099:ℚ)/468750000000000000000000),((-430013479:ℚ)/1024000000)⟩
theorem valid17 : Valid source33 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9004095541:ℚ)/10000000000),((3229522567:ℚ)/2500000000),((39628350317:ℚ)/73600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-3066555259526691:ℚ)/18400000000000000),((-430013479:ℚ)/1024000000)⟩
theorem valid18 : Valid source33 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC28
#check @N11Formalization.C450Source33GroupedC28.bound
#print axioms N11Formalization.C450Source33GroupedC28.valid0
#print axioms N11Formalization.C450Source33GroupedC28.valid1
#print axioms N11Formalization.C450Source33GroupedC28.valid2
#print axioms N11Formalization.C450Source33GroupedC28.valid3
#print axioms N11Formalization.C450Source33GroupedC28.valid4
#print axioms N11Formalization.C450Source33GroupedC28.valid5
#print axioms N11Formalization.C450Source33GroupedC28.valid6
#print axioms N11Formalization.C450Source33GroupedC28.valid7
#print axioms N11Formalization.C450Source33GroupedC28.valid8
#print axioms N11Formalization.C450Source33GroupedC28.valid9
#print axioms N11Formalization.C450Source33GroupedC28.valid10
#print axioms N11Formalization.C450Source33GroupedC28.valid11
#print axioms N11Formalization.C450Source33GroupedC28.valid12
#print axioms N11Formalization.C450Source33GroupedC28.valid13
#print axioms N11Formalization.C450Source33GroupedC28.valid14
#print axioms N11Formalization.C450Source33GroupedC28.valid15
#print axioms N11Formalization.C450Source33GroupedC28.valid16
#print axioms N11Formalization.C450Source33GroupedC28.valid17
#print axioms N11Formalization.C450Source33GroupedC28.valid18
#print axioms N11Formalization.C450Source33GroupedC28.bound
#print axioms N11Formalization.C450Source33GroupedC28.endpoint_checks
