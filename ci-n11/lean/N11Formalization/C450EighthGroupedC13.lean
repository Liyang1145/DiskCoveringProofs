import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((3120258261:ℚ)/5000000000),((6501788731:ℚ)/10000000000),((-5541788731:ℚ)/24800000000),((-7120774783:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1518561789:ℚ)/2500000000),((1197409156891702198094097044983199896224565908781490117117:ℚ)/79393446093750000000000000000000000000000000000000000000000),((7031902140668690052675333:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((1295636409:ℚ)/2000000000),((421218257:ℚ)/625000000),((-361218257:ℚ)/1609375000),((-2990909227:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2751263859:ℚ)/5000000000),((23467212325044039313435303361180188091279932107989234603:ℚ)/1568415031200000000000000000000000000000000000000000000000),((26799357830871053267397:ℚ)/902500000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6715835777:ℚ)/10000000000),((214323077:ℚ)/312500000),((-184323077:ℚ)/834375000),((-15667507331:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2435834969:ℚ)/5000000000),((10503531801288726511982874174852326627571927848488907197253:ℚ)/714428311043750000000000000000000000000000000000000000000000),((6521250684059464840787:ℚ)/225625000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((6834658609:ℚ)/10000000000),((6977181501:ℚ)/10000000000),((-6017181501:ℚ)/27175000000),((-16023975827:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((90527301:ℚ)/200000000),((6315897943682248262579193863516409266685250979994197735809:ℚ)/430840204216406250000000000000000000000000000000000000000000),((1040947969271683758699461:ℚ)/36480000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((869184867:ℚ)/1250000000),((7036601829:ℚ)/10000000000),((-6076601829:ℚ)/27650000000),((-2047554601:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4154583089:ℚ)/10000000000),((8517621852187650540600814796937711247423180536148400119:ℚ)/585630826208400726318359375000000000000000000000000000000),((19504276798303558379539919:ℚ)/693120000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7012888201:ℚ)/10000000000),((443501337:ℚ)/625000000),((-383501337:ℚ)/1742968750),((-16558664603:ℚ)/112500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3956442831:ℚ)/10000000000),((3379766615785585670895616424860210490432032551725060334977:ℚ)/232658243179321289062500000000000000000000000000000000000000),((75691593437497194907871:ℚ)/2707500000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((3536148443:ℚ)/5000000000),((7155440207:ℚ)/10000000000),((-6195440207:ℚ)/28125000000),((-8368445329:ℚ)/56725000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1874211389:ℚ)/5000000000),((124144434083813199246513226383721656483868795581154541:ℚ)/8555882159912109375000000000000000000000000000000000000),((6416660312153495261546797:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-1:ℚ)/4),((-3:ℚ)/16),((7131705007:ℚ)/10000000000),((359257467:ℚ)/500000000),((-311257467:ℚ)/1418125000),((-345206429:ℚ)/2325000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((44109651:ℚ)/125000000),((858883660021825914830008477182917707759907568364058461:ℚ)/59410352636718750000000000000000000000000000000000000000),((47783348250003271329551:ℚ)/1732800000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((358070443:ℚ)/500000000),((3607429147:ℚ)/5000000000),((-3127429147:ℚ)/14240625000),((-77291939:ℚ)/520000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3413887111:ℚ)/10000000000),((19288151700104169581037625094645121960383476304506267:ℚ)/1334897200000000000000000000000000000000000000000000000),((1587492275477367244811077:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-1:ℚ)/4),((-3:ℚ)/16),((7191112577:ℚ)/10000000000),((7244567069:ℚ)/10000000000),((-571324279:ℚ)/2600000000),((-17093337731:ℚ)/114875000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((411895179:ℚ)/1250000000),((5336288475749110962928284143080157729565431523949604639707:ℚ)/369505747082519531250000000000000000000000000000000000000000),((6328838587539611769356533:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((45130101:ℚ)/62500000),((727427567:ℚ)/1000000000),((-631427567:ℚ)/2871875000),((-107390303:ℚ)/720937500),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3172163279:ℚ)/10000000000),((910139076958846126098504870055453773992878467703:ℚ)/63053569229973480105400085449218750000000000000000),((63077215555584789076717:ℚ)/2310400000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((725051961:ℚ)/1000000000),((7333692353:ℚ)/10000000000),((-6373692353:ℚ)/28837500000),((-1727155883:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1522187141:ℚ)/5000000000),((109347236504242172472741451387496222223311824702940719389:ℚ)/7560412671518750000000000000000000000000000000000000000000),((6289916996603301649648077:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((182748153:ℚ)/250000000),((184827709:ℚ)/250000000),((-160827709:ℚ)/726875000),((-62320637:ℚ)/418750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2771747183:ℚ)/10000000000),((23135484273923643839969961936253200349855372114036571:ℚ)/1601199504089355468750000000000000000000000000000000000),((3904860672895646730293:ℚ)/144400000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((3684666059:ℚ)/5000000000),((7452523707:ℚ)/10000000000),((-6492523707:ℚ)/29312500000),((-8813998177:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((61751339:ℚ)/250000000),((727873790110528706683345103330401874455011127680956297713:ℚ)/50423624114062500000000000000000000000000000000000000000000),((18617073197753477620261391:ℚ)/693120000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((3714368809:ℚ)/5000000000),((1514270497:ℚ)/2000000000),((-1322270497:ℚ)/5910000000),((-8903106427:ℚ)/60050000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((106347709:ℚ)/500000000),((2897603762076115919602406442528344840938852900473384209251:ℚ)/199961571912304687500000000000000000000000000000000000000000),((246818300791416872699277:ℚ)/9241600000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((7547547169:ℚ)/10000000000),((3845089403:ℚ)/5000000000),((-3365089403:ℚ)/15012500000),((-18162641507:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((587777247:ℚ)/5000000000),((591475111850944097418747340261223595136650590368594181995783:ℚ)/40890627150000000000000000000000000000000000000000000000000000),((399750099477789:ℚ)/15200000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((479147179:ℚ)/625000000),((4082730847:ℚ)/5000000000),((-3602730847:ℚ)/15250000000),((-1157441537:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1000999751071542606201752747374502141740899369047103577:ℚ)/67537293750000000000000000000000000000000000000000000000),((417807:ℚ)/16000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((1628313743:ℚ)/2000000000),((10066324327:ℚ)/10000000000),((-9106324327:ℚ)/32400000000),((-3988941229:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((88380203545863255207883834495374657666998444287589880601:ℚ)/5529600000000000000000000000000000000000000000000000000000),((417807:ℚ)/16000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10042220861:ℚ)/10000000000),((6933668351:ℚ)/5000000000),((-6453668351:ℚ)/20000000000),((-25646662583:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((897560626592521912726881690299624703437905005606570814147:ℚ)/50458982400000000000000000000000000000000000000000000000000),((417807:ℚ)/16000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC13
#check @N11Formalization.C450EighthGroupedC13.bound
#print axioms N11Formalization.C450EighthGroupedC13.valid0
#print axioms N11Formalization.C450EighthGroupedC13.valid1
#print axioms N11Formalization.C450EighthGroupedC13.valid2
#print axioms N11Formalization.C450EighthGroupedC13.valid3
#print axioms N11Formalization.C450EighthGroupedC13.valid4
#print axioms N11Formalization.C450EighthGroupedC13.valid5
#print axioms N11Formalization.C450EighthGroupedC13.valid6
#print axioms N11Formalization.C450EighthGroupedC13.valid7
#print axioms N11Formalization.C450EighthGroupedC13.valid8
#print axioms N11Formalization.C450EighthGroupedC13.valid9
#print axioms N11Formalization.C450EighthGroupedC13.valid10
#print axioms N11Formalization.C450EighthGroupedC13.valid11
#print axioms N11Formalization.C450EighthGroupedC13.valid12
#print axioms N11Formalization.C450EighthGroupedC13.valid13
#print axioms N11Formalization.C450EighthGroupedC13.valid14
#print axioms N11Formalization.C450EighthGroupedC13.valid15
#print axioms N11Formalization.C450EighthGroupedC13.valid16
#print axioms N11Formalization.C450EighthGroupedC13.valid17
#print axioms N11Formalization.C450EighthGroupedC13.valid18
#print axioms N11Formalization.C450EighthGroupedC13.bound
#print axioms N11Formalization.C450EighthGroupedC13.endpoint_checks
