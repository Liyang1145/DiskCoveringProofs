import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/4),((5:ℚ)/16),((5638911689:ℚ)/10000000000),((2989675351:ℚ)/5000000000),((10918911689:ℚ)/25750000000),((5165675351:ℚ)/9920000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3674020821:ℚ)/5000000000),((-32831693318883009387782430287765536541684358069746710807961:ℚ)/102549867871093750000000000000000000000000000000000000000000),((-15811826095160697495170513:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((5881538767:ℚ)/10000000000),((3050233821:ℚ)/5000000000),((11161538767:ℚ)/26225000000),((5226233821:ℚ)/10300000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((3429205123:ℚ)/5000000000),((-95746684699072474777600454858131684732605948656418539440327:ℚ)/298979193487329101562500000000000000000000000000000000000000),((-16012912709524034496975433:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((1500677173:ℚ)/2500000000),((6221497923:ℚ)/10000000000),((2820677173:ℚ)/6675000000),((10573497923:ℚ)/20980000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((82533051:ℚ)/125000000),((-18020581655372368492825491431575362793373833844074734582437:ℚ)/56817523869799804687500000000000000000000000000000000000000),((-64102616766898368560419177:ℚ)/184832000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3061894981:ℚ)/5000000000),((317122313:ℚ)/500000000),((5701894981:ℚ)/13587500000),((178240771:ℚ)/356000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((19807363:ℚ)/31250000),((-39026110412601332529191482459578618372269194798576912031989:ℚ)/124187733755651855468750000000000000000000000000000000000000),((-160350033164021833153697:ℚ)/462080000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1248957481:ℚ)/2000000000),((6463317031:ℚ)/10000000000),((2304957481:ℚ)/5530000000),((10815317031:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6064394291:ℚ)/10000000000),((-6078272081920952181605122294137409502490604493186733856249:ℚ)/19513470915968066406250000000000000000000000000000000000000),((-64163871088394663137997393:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((3182852751:ℚ)/5000000000),((6584114303:ℚ)/10000000000),((646983639:ℚ)/1562500000),((10936114303:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5779344619:ℚ)/10000000000),((-15907864364912160721930407542496688429419470785742283:ℚ)/51502138376235961914062500000000000000000000000000000),((-64174218793316484133755617:ℚ)/184832000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((3243274209:ℚ)/5000000000),((6704841863:ℚ)/10000000000),((5883274209:ℚ)/14300000000),((11056841863:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5481439:ℚ)/10000000),((-151197565582965559242773677941404678584255725879015712267:ℚ)/493459931250000000000000000000000000000000000000000000000),((-64171082915781001389454097:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6607320027:ℚ)/10000000000),((6825503239:ℚ)/10000000000),((11887320027:ℚ)/29075000000),((11177503239:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5168415613:ℚ)/10000000000),((-955145135065491191160974562942717084963742849411262328279507:ℚ)/3141313368008105468750000000000000000000000000000000000000000),((-64154488147210402687491473:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6728023943:ℚ)/10000000000),((6946101723:ℚ)/10000000000),((12008023943:ℚ)/29550000000),((11298101723:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4837300257:ℚ)/10000000000),((-1828881464233260535616623945323431429284279569353890041502703:ℚ)/6059117878849804687500000000000000000000000000000000000000000),((-64124457523067522135451577:ℚ)/184832000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((1369732707:ℚ)/2000000000),((57496977:ℚ)/80000000),((2425732707:ℚ)/6100000000),((92312977:ℚ)/189120000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((448404511:ℚ)/1000000000),((-16239671644216271426890182371607497411721527653157711267883:ℚ)/55055660181250000000000000000000000000000000000000000000000),((-4050507488096533358977:ℚ)/11829248000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((886220267:ℚ)/1250000000),((3834265559:ℚ)/5000000000),((1546220267:ℚ)/4050000000),((6010265559:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3685146599:ℚ)/10000000000),((-16186454400108749724552455787893400277755440778190981481:ℚ)/57219096093750000000000000000000000000000000000000000000),((-1630098649574959:ℚ)/4864000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((757131321:ℚ)/1000000000),((958798871:ℚ)/1000000000),((1285131321:ℚ)/4000000000),((1393998871:ℚ)/2592000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((434566141:ℚ)/5000000000),((-70126258540365383924142162117421523642546322571767330641:ℚ)/291600000000000000000000000000000000000000000000000000000),((-1365875261418917:ℚ)/3891200000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9491200127:ℚ)/10000000000),((6705343879:ℚ)/5000000000),((14771200127:ℚ)/55200000000),((8881343879:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-17916686749863424753187199480243548857257901106325455549:ℚ)/87602400000000000000000000000000000000000000000000000000),((-45051203:ℚ)/128000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC21
#check @N11Formalization.C450Source35GroupedC21.bound
#print axioms N11Formalization.C450Source35GroupedC21.valid0
#print axioms N11Formalization.C450Source35GroupedC21.valid1
#print axioms N11Formalization.C450Source35GroupedC21.valid2
#print axioms N11Formalization.C450Source35GroupedC21.valid3
#print axioms N11Formalization.C450Source35GroupedC21.valid4
#print axioms N11Formalization.C450Source35GroupedC21.valid5
#print axioms N11Formalization.C450Source35GroupedC21.valid6
#print axioms N11Formalization.C450Source35GroupedC21.valid7
#print axioms N11Formalization.C450Source35GroupedC21.valid8
#print axioms N11Formalization.C450Source35GroupedC21.valid9
#print axioms N11Formalization.C450Source35GroupedC21.valid10
#print axioms N11Formalization.C450Source35GroupedC21.valid11
#print axioms N11Formalization.C450Source35GroupedC21.valid12
#print axioms N11Formalization.C450Source35GroupedC21.bound
#print axioms N11Formalization.C450Source35GroupedC21.endpoint_checks
