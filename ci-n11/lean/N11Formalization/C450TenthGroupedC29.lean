import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((737993383:ℚ)/1250000000),((6431643353:ℚ)/10000000000),((2373980149:ℚ)/3337500000),((89371363589:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3405860791:ℚ)/5000000000),((-76274949512726862324448170846220079:ℚ)/3717609960937500000000000000000000000),((-2260573896474429902245957:ℚ)/12160000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((797400003:ℚ)/1250000000),((416828671:ℚ)/625000000),((2552200009:ℚ)/3456250000),((5778772723:ℚ)/6675000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1436690169:ℚ)/2500000000),((-2616689019916306477331267225770740283339333458941359:ℚ)/110590718078613281250000000000000000000000000000000000),((-42849361303129990348557223:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((3308406729:ℚ)/5000000000),((6788063503:ℚ)/10000000000),((10565220187:ℚ)/14062500000),((94004825539:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5143079967:ℚ)/10000000000),((-145671602063003010237635052672074261357673582809233331:ℚ)/5793571472167968750000000000000000000000000000000000000),((-684785722750178108933416927:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((67356173:ℚ)/100000000),((6906866449:ℚ)/10000000000),((214868519:ℚ)/286000000),((95549263837:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((240788673:ℚ)/500000000),((-334550012519527229010219052245193544342782759919:ℚ)/13291850000000000000000000000000000000000000000000),((-273563351329127374579463:ℚ)/1478656000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6854419351:ℚ)/10000000000),((6966267267:ℚ)/10000000000),((21843258053:ℚ)/28837500000),((96321474471:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((893308791:ℚ)/2000000000),((-2908569520299047161385226426894608846208206391323488829:ℚ)/112412369778442382812500000000000000000000000000000000000),((-2734039214386584223459711647:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3456909867:ℚ)/5000000000),((439104229:ℚ)/625000000),((11010729601:ℚ)/14537500000),((6068354977:ℚ)/7209375000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4282036639:ℚ)/10000000000),((-19876539129583564393243796061812925530363578616155579:ℚ)/768084837402343750000000000000000000000000000000000000),((-683072344637882186952904183:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((6973219701:ℚ)/10000000000),((55352091:ℚ)/78125000),((22199659103:ℚ)/29312500000),((764577183:ℚ)/908593750),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((4089750191:ℚ)/10000000000),((-436509933042453352940352291570125484086513367128798393:ℚ)/16865600967407226562500000000000000000000000000000000000),((-2730540932681397652821957047:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((27471169:ℚ)/39062500),((7144467231:ℚ)/10000000000),((174827014:ℚ)/230859375),((14091153429:ℚ)/16750000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1944263517:ℚ)/5000000000),((-110585393663196830525371367323695187412055219197:ℚ)/4272185079753398895263671875000000000000000000000),((-70127309734643277293751:ℚ)/380000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((7092018431:ℚ)/10000000000),((3601933211:ℚ)/5000000000),((22556055293:ℚ)/29787500000),((49705131743:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1838448181:ℚ)/5000000000),((-12829252929323813820897900095595609494990529781901531549:ℚ)/495568208752441406250000000000000000000000000000000000000),((-2727048209395377252637729967:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((7151417213:ℚ)/10000000000),((7263265229:ℚ)/10000000000),((22734251639:ℚ)/30025000000),((100182447977:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1726470489:ℚ)/5000000000),((-273748785488299771303476671125268829023002241643373781:ℚ)/10573264166259765625000000000000000000000000000000000000),((-2725303931430202346630735143:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((7210815619:ℚ)/10000000000),((7322663663:ℚ)/10000000000),((22912446857:ℚ)/30262500000),((100954627619:ℚ)/120100000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((321408123:ℚ)/1000000000),((-498350998909916851645335916529182807759866138950227603:ℚ)/19246506701660156250000000000000000000000000000000000000),((-2723561042143854656011625767:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((7270213657:ℚ)/10000000000),((7382061731:ℚ)/10000000000),((23090640971:ℚ)/30500000000),((101726802503:ℚ)/121050000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((591340493:ℚ)/2000000000),((-4591964259707617649504653022695621988358823527754835529:ℚ)/177328906250000000000000000000000000000000000000000000000),((-2721819541307856654602026303:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((916201417:ℚ)/1250000000),((7500856807:ℚ)/10000000000),((415514893:ℚ)/553125000),((103271138491:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2675460323:ℚ)/10000000000),((-2227142309529508009475868450929577394111600134061:ℚ)/88139104843139648437500000000000000000000000000000),((-42471406401851519964403583:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((7448405649:ℚ)/10000000000),((190491263:ℚ)/250000000),((23625216947:ℚ)/31450000000),((374340917:ℚ)/442500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((125041529:ℚ)/625000000),((-4800320502635994957301623813979253648093847885436473:ℚ)/189863730621337890625000000000000000000000000000000000),((-2715325665299288624296661647:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((236474957:ℚ)/312500000),((3928617049:ℚ)/5000000000),((749424871:ℚ)/1012500000),((53952021637:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((185883377:ℚ)/2000000000),((-5797190029010707976613101246900548419016065975503:ℚ)/240270996093750000000000000000000000000000000000000),((-2652025328910358284061703:ℚ)/14440000000000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7804780791:ℚ)/10000000000),((1219719969:ℚ)/1250000000),((24694342373:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-935754280954065421640275775979881751482467031152571381:ℚ)/75000000000000000000000000000000000000000000000000000000),((-188072789:ℚ)/1024000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((9705297567:ℚ)/10000000000),((13558376719:ℚ)/10000000000),((30395892701:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-233375736457559036438913010048997173:ℚ)/42049152000000000000000000000000000000),((-188072789:ℚ)/1024000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC29
#check @N11Formalization.C450TenthGroupedC29.bound
#print axioms N11Formalization.C450TenthGroupedC29.valid0
#print axioms N11Formalization.C450TenthGroupedC29.valid1
#print axioms N11Formalization.C450TenthGroupedC29.valid2
#print axioms N11Formalization.C450TenthGroupedC29.valid3
#print axioms N11Formalization.C450TenthGroupedC29.valid4
#print axioms N11Formalization.C450TenthGroupedC29.valid5
#print axioms N11Formalization.C450TenthGroupedC29.valid6
#print axioms N11Formalization.C450TenthGroupedC29.valid7
#print axioms N11Formalization.C450TenthGroupedC29.valid8
#print axioms N11Formalization.C450TenthGroupedC29.valid9
#print axioms N11Formalization.C450TenthGroupedC29.valid10
#print axioms N11Formalization.C450TenthGroupedC29.valid11
#print axioms N11Formalization.C450TenthGroupedC29.valid12
#print axioms N11Formalization.C450TenthGroupedC29.valid13
#print axioms N11Formalization.C450TenthGroupedC29.valid14
#print axioms N11Formalization.C450TenthGroupedC29.valid15
#print axioms N11Formalization.C450TenthGroupedC29.valid16
#print axioms N11Formalization.C450TenthGroupedC29.bound
#print axioms N11Formalization.C450TenthGroupedC29.endpoint_checks
