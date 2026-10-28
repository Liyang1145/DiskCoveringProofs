import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/4),((13:ℚ)/16),((5325285647:ℚ)/10000000000),((282671463:ℚ)/500000000),((19975856941:ℚ)/25750000000),((4506729019:ℚ)/4960000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((993030623:ℚ)/1250000000),((-103948896534528900861596511038975488617:ℚ)/341477187500000000000000000000000000000),((-236555605377597979153767:ℚ)/577600000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((2781943447:ℚ)/5000000000),((2946073811:ℚ)/5000000000),((10345830341:ℚ)/13350000000),((46618959543:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7494107747:ℚ)/10000000000),((-5892646052235897741518169935758205092129738640925769:ℚ)/19362551879882812500000000000000000000000000000000000),((-23287638015747879193401103:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((5802409267:ℚ)/10000000000),((93929291:ℚ)/156250000),((21407227801:ℚ)/27175000000),((1481080783:ℚ)/1668750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1404239457:ℚ)/2000000000),((-40027237316591161350213931804318263821665337141491547183:ℚ)/125426318652343750000000000000000000000000000000000000000),((-22560241976388612211133:ℚ)/56406250000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((5921643483:ℚ)/10000000000),((3065390831:ℚ)/5000000000),((21764930449:ℚ)/27650000000),((48170080803:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6774659459:ℚ)/10000000000),((-2631560296359548460383552448270856990648463765345475183:ℚ)/8257440283203125000000000000000000000000000000000000000),((-22914410203218623976339223:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((1510215241:ℚ)/2500000000),((6250069757:ℚ)/10000000000),((5530645723:ℚ)/7031250000),((13984415263:ℚ)/15800000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1304071549:ℚ)/2000000000),((-8536398202521936483368302189056732214132995941284189:ℚ)/26822090148925781250000000000000000000000000000000000),((-90903217342864489135225007:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1540015641:ℚ)/2500000000),((6309707:ℚ)/10000000),((5620046923:ℚ)/7090625000),((98666191:ℚ)/112500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6257321081:ℚ)/10000000000),((-724316366795838803557014419593721829422091903969058589:ℚ)/2228094312477111816406250000000000000000000000000000000),((-90524012080766487407:ℚ)/231040000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((310982883:ℚ)/500000000),((318466993:ℚ)/500000000),((1132948649:ℚ)/1430000000),((4972070909:ℚ)/5672500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1530542281:ℚ)/2500000000),((-1660415633219736174567880691325854854590296034761:ℚ)/5112250000000000000000000000000000000000000000000),((-225358693083677817214007:ℚ)/577600000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6279249081:ℚ)/10000000000),((1607242111:ℚ)/2500000000),((22837747243:ℚ)/28837500000),((1927242111:ℚ)/2200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1496093203:ℚ)/2500000000),((-4053141310572564454247711093177536597439088286395540407:ℚ)/12490263308715820312500000000000000000000000000000000000),((-5610100775864584958482903:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6338836917:ℚ)/10000000000),((324429643:ℚ)/500000000),((23016510751:ℚ)/29075000000),((5049585359:ℚ)/5767500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((5843742001:ℚ)/10000000000),((-1992232211858613689984202994824649585377462734737141993:ℚ)/6144678699218750000000000000000000000000000000000000000),((-223446043046267281106207:ℚ)/577600000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((3199210629:ℚ)/5000000000),((654821321:ℚ)/1000000000),((11597631887:ℚ)/14656250000),((10176677173:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1425015943:ℚ)/2500000000),((-227644408180888397275553870055635650796265556335939903:ℚ)/702733373641967773437500000000000000000000000000000000),((-889938912730589056629863:ℚ)/2310400000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6458002189:ℚ)/10000000000),((6607829591:ℚ)/10000000000),((23374006567:ℚ)/29550000000),((102541784683:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2776549213:ℚ)/5000000000),((-4349787774742973899937137181358824028202106490984035347:ℚ)/13439132226562500000000000000000000000000000000000000000),((-88608034226170527756830183:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6517579793:ℚ)/10000000000),((66674421:ℚ)/100000000),((23552739379:ℚ)/29787500000),((1033167473:ℚ)/1182000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((675321813:ℚ)/1250000000),((-53421253644478408664984781706415485788438202833484336197:ℚ)/165189402917480468750000000000000000000000000000000000000),((-8822084571767514458463:ℚ)/23104000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((131543083:ℚ)/200000000),((6727050829:ℚ)/10000000000),((474629249:ℚ)/600500000),((104091660777:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1312045641:ℚ)/2500000000),((-27331939402932617478626422719862088172611128552767:ℚ)/84586113330078125000000000000000000000000000000000),((-87832325411205846877944463:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((6636725337:ℚ)/10000000000),((1369251461:ℚ)/2000000000),((23910176011:ℚ)/30500000000),((21128268993:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5089567291:ℚ)/10000000000),((-56078153450727189990643511057942081498967299785879562253:ℚ)/177328906250000000000000000000000000000000000000000000000),((-3482051523307073297225503:ℚ)/9241600000000000000000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3377929251:ℚ)/5000000000),((3482724851:ℚ)/5000000000),((12133787753:ℚ)/15487500000),((53595423063:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((4757952323:ℚ)/10000000000),((-611124002383673165905316661954941253650805962279270357:ℚ)/1934829629516601562500000000000000000000000000000000000),((-21566229933527465219633743:ℚ)/57760000000000000000000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6874979859:ℚ)/10000000000),((7084628663:ℚ)/10000000000),((24624939577:ℚ)/31450000000),((108740172619:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4403498031:ℚ)/10000000000),((-59897400530570778924005462715235138102842891619446111:ℚ)/189863730621337890625000000000000000000000000000000000),((-85473218001126354711283367:ℚ)/231040000000000000000000000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((1748522487:ℚ)/2500000000),((3661474329:ℚ)/5000000000),((6245567461:ℚ)/8100000000),((55919166277:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4020136037:ℚ)/10000000000),((-12428479331890327758012838636538295366015144626915107:ℚ)/41006250000000000000000000000000000000000000000000000),((-20968451407213935497003463:ℚ)/57760000000000000000000000)⟩
theorem valid16 : Valid source27 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((3616139157:ℚ)/5000000000),((288378157:ℚ)/312500000),((12848417471:ℚ)/20000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3123450717:ℚ)/10000000000),((-572935196746816912438986005832040071108918063804671697:ℚ)/3125000000000000000000000000000000000000000000000000000),((-11355569:ℚ)/32000000)⟩
theorem valid17 : Valid source27 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((9136604327:ℚ)/10000000000),((13034139439:ℚ)/10000000000),((31409812981:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1550906129901406603818160561810577227:ℚ)/14016384000000000000000000000000000000),((-11355569:ℚ)/32000000)⟩
theorem valid18 : Valid source27 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source27 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC29
#check @N11Formalization.C450Source27GroupedC29.bound
#print axioms N11Formalization.C450Source27GroupedC29.valid0
#print axioms N11Formalization.C450Source27GroupedC29.valid1
#print axioms N11Formalization.C450Source27GroupedC29.valid2
#print axioms N11Formalization.C450Source27GroupedC29.valid3
#print axioms N11Formalization.C450Source27GroupedC29.valid4
#print axioms N11Formalization.C450Source27GroupedC29.valid5
#print axioms N11Formalization.C450Source27GroupedC29.valid6
#print axioms N11Formalization.C450Source27GroupedC29.valid7
#print axioms N11Formalization.C450Source27GroupedC29.valid8
#print axioms N11Formalization.C450Source27GroupedC29.valid9
#print axioms N11Formalization.C450Source27GroupedC29.valid10
#print axioms N11Formalization.C450Source27GroupedC29.valid11
#print axioms N11Formalization.C450Source27GroupedC29.valid12
#print axioms N11Formalization.C450Source27GroupedC29.valid13
#print axioms N11Formalization.C450Source27GroupedC29.valid14
#print axioms N11Formalization.C450Source27GroupedC29.valid15
#print axioms N11Formalization.C450Source27GroupedC29.valid16
#print axioms N11Formalization.C450Source27GroupedC29.valid17
#print axioms N11Formalization.C450Source27GroupedC29.valid18
#print axioms N11Formalization.C450Source27GroupedC29.bound
#print axioms N11Formalization.C450Source27GroupedC29.endpoint_checks
