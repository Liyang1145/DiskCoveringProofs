import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((1360936711:ℚ)/2500000000),((5999851839:ℚ)/10000000000),((3682185659:ℚ)/4450000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((61786887:ℚ)/80000000),((-676738711804009061558266041372077393:ℚ)/4406056250000000000000000000000000000),((-40983852095512796017940611:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((5919192227:ℚ)/10000000000),((3118850507:ℚ)/5000000000),((47514345589:ℚ)/55300000000),((10636551521:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1355960673:ℚ)/2000000000),((-185254380506814504960820021492914412368611201494214093709:ℚ)/1056952356250000000000000000000000000000000000000000000000),((-33876666052213353451832681:ℚ)/97280000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((192402873:ℚ)/312500000),((202360217:ℚ)/312500000),((1536820111:ℚ)/1787500000),((687080651:ℚ)/691250000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((313222029:ℚ)/500000000),((-6257031050472332238446711081612676477768936352179879:ℚ)/35695886230468750000000000000000000000000000000000000),((-97363082975249472656243:ℚ)/285000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3197289181:ℚ)/5000000000),((3297215953:ℚ)/5000000000),((25421024267:ℚ)/29075000000),((11171647859:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((89209797:ℚ)/156250000),((-28439556402133007000600984671182851473530145009232915403:ℚ)/153616967480468750000000000000000000000000000000000000000),((-156351567742478371313813451:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6513417001:ℚ)/10000000000),((6713331877:ℚ)/10000000000),((17224639669:ℚ)/19700000000),((22699995631:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((84581469:ℚ)/156250000),((-2209369347755212270738190184605160995001789278987792381:ℚ)/11945895312500000000000000000000000000000000000000000000),((-619300135501940038922416291:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6632252787:ℚ)/10000000000),((3386390033:ℚ)/5000000000),((52505769509:ℚ)/59575000000),((11439170099:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5101631697:ℚ)/10000000000),((-250680329174947642318324225350943349274078589794958022349:ℚ)/1321515223339843750000000000000000000000000000000000000000),((-1848874179975284751053667137:ℚ)/5544960000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6691669653:ℚ)/10000000000),((3416113547:ℚ)/5000000000),((52921687571:ℚ)/60050000000),((11528340641:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2469582933:ℚ)/5000000000),((-64136657696390884596396978893629684228690885712334688419:ℚ)/338344453320312500000000000000000000000000000000000000000),((-1839719557451305056143471057:ℚ)/5544960000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((210971433:ℚ)/312500000),((689167299:ℚ)/1000000000),((1666800031:ℚ)/1891406250),((2323501897:ℚ)/2402000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((4771644123:ℚ)/10000000000),((-1001388185687224307687350790825651332704389997228757:ℚ)/5286210947111248970031738281250000000000000000000000),((-1787662391130634788704897:ℚ)/5415000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((1702625353:ℚ)/2500000000),((347555889:ℚ)/500000000),((13438377471:ℚ)/15250000000),((1170667667:ℚ)/1210500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((71851729:ℚ)/156250000),((-4196328622494211335914042183540488238814960536325393039:ℚ)/22166113281250000000000000000000000000000000000000000000),((-37946132689790053468709219:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((429369771:ℚ)/625000000),((7010561489:ℚ)/10000000000),((3385588397:ℚ)/3842187500),((23591684467:ℚ)/24400000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((552387819:ℚ)/1250000000),((-4191877696891188616911554975872908021396336300167593:ℚ)/22156221537292003631591796875000000000000000000000000),((-372587128971669591981947:ℚ)/1140000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3464665321:ℚ)/5000000000),((441875259:ℚ)/625000000),((27292657247:ℚ)/30975000000),((1485625777:ℚ)/1536875000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((4232618501:ℚ)/10000000000),((-11707099418748376540420859867097929685804591254415230381:ℚ)/61914548144531250000000000000000000000000000000000000000),((-150259546909956967111216931:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((873593043:ℚ)/1250000000),((7188886381:ℚ)/10000000000),((6875151301:ℚ)/7862500000),((24126659143:ℚ)/24780000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((504759333:ℚ)/1250000000),((-140015474173967834889468098759823009768485727007363101:ℚ)/759454922485351562500000000000000000000000000000000000),((-27885639692220349393802177:ℚ)/86640000000000000000000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3553784997:ℚ)/5000000000),((7307764677:ℚ)/10000000000),((27916494979:ℚ)/31925000000),((24483294031:ℚ)/25160000000),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((1809771631:ℚ)/5000000000),((-2341884546858038469271485493942880326072944982286697131:ℚ)/12710210772705078125000000000000000000000000000000000000),((-441597363722051601040671857:ℚ)/1386240000000000000000000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((7226393391:ℚ)/10000000000),((3713319603:ℚ)/5000000000),((56664753737:ℚ)/64800000000),((12419958809:ℚ)/12770000000),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((393568979:ℚ)/1250000000),((-34797196161439533329842184937003242171634490813938385153:ℚ)/188956800000000000000000000000000000000000000000000000000),((-1748103264854312121336309113:ℚ)/5544960000000000000000000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((7345214633:ℚ)/10000000000),((395105139:ℚ)/500000000),((57496502431:ℚ)/68600000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((519333399:ℚ)/2000000000),((-20190860535592547978059669754578741812558748331395970519:ℚ)/126105021875000000000000000000000000000000000000000000000),((-573770004960067072960942499:ℚ)/1848320000000000000000000000)⟩
theorem valid14 : Valid source21 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((488779991:ℚ)/625000000),((2094379407:ℚ)/2500000000),((3801459937:ℚ)/4525000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-3737175190951475544121647046919256965066669767931553:ℚ)/23163050781250000000000000000000000000000000000000000),((-39749433:ℚ)/128000000)⟩
theorem valid15 : Valid source21 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source21 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((259241163:ℚ)/312500000),((58301431:ℚ)/62500000),((2004688141:ℚ)/2500000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-3365204361265980844849758123322338025283218671491029:ℚ)/24414062500000000000000000000000000000000000000000000),((-39749433:ℚ)/128000000)⟩
theorem valid16 : Valid source21 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source21 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((4623062123:ℚ)/5000000000),((13130094239:ℚ)/10000000000),((11800478287:ℚ)/18400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-72667621617810771155249964445286541:ℚ)/1557376000000000000000000000000000000),((-39749433:ℚ)/128000000)⟩
theorem valid17 : Valid source21 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2383:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((61:ℚ)/80) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source21 nn0 nn1 Qcell ((1239:ℚ)/1600) ((1277:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((1277:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source21 nn0 nn1 Qcell ((1277:ℚ)/1600) ((343:ℚ)/400) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source21 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source21 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source21 nn0 nn1 Qcell ((1277:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC31
#check @N11Formalization.C450Source21GroupedC31.bound
#print axioms N11Formalization.C450Source21GroupedC31.valid0
#print axioms N11Formalization.C450Source21GroupedC31.valid1
#print axioms N11Formalization.C450Source21GroupedC31.valid2
#print axioms N11Formalization.C450Source21GroupedC31.valid3
#print axioms N11Formalization.C450Source21GroupedC31.valid4
#print axioms N11Formalization.C450Source21GroupedC31.valid5
#print axioms N11Formalization.C450Source21GroupedC31.valid6
#print axioms N11Formalization.C450Source21GroupedC31.valid7
#print axioms N11Formalization.C450Source21GroupedC31.valid8
#print axioms N11Formalization.C450Source21GroupedC31.valid9
#print axioms N11Formalization.C450Source21GroupedC31.valid10
#print axioms N11Formalization.C450Source21GroupedC31.valid11
#print axioms N11Formalization.C450Source21GroupedC31.valid12
#print axioms N11Formalization.C450Source21GroupedC31.valid13
#print axioms N11Formalization.C450Source21GroupedC31.valid14
#print axioms N11Formalization.C450Source21GroupedC31.valid15
#print axioms N11Formalization.C450Source21GroupedC31.valid16
#print axioms N11Formalization.C450Source21GroupedC31.valid17
#print axioms N11Formalization.C450Source21GroupedC31.bound
#print axioms N11Formalization.C450Source21GroupedC31.endpoint_checks
