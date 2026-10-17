import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((6092543901:ℚ)/10000000000),((412468257:ℚ)/625000000),((7212543901:ℚ)/26700000000),((476468257:ℚ)/1240000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6407451867:ℚ)/10000000000),((438889798970073440014076392728614453:ℚ)/33980329584000000000000000000000000000),((-60621696425931938591272139:ℚ)/693120000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6568075057:ℚ)/10000000000),((6837181501:ℚ)/10000000000),((7688075057:ℚ)/27650000000),((7861181501:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1054395141:ℚ)/2000000000),((649354689213238313374364335441037624447932911329079093707489:ℚ)/55879856187523200000000000000000000000000000000000000000000000),((-20785785117395452543237937:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((6805813219:ℚ)/10000000000),((434751337:ℚ)/625000000),((7925813219:ℚ)/28125000000),((71250191:ℚ)/197500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2306195213:ℚ)/5000000000),((43177040300991870599711042786525408171518288107433:ℚ)/3900015527343750000000000000000000000000000000000000),((-21077172705191084981952793:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((3462338129:ℚ)/5000000000),((7015440207:ℚ)/10000000000),((4022338129:ℚ)/14181250000),((8039440207:ℚ)/22500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4247504171:ℚ)/10000000000),((3964838784391407956899627449367311104258031559080326616243089:ℚ)/366519059472656250000000000000000000000000000000000000000000000),((-5305848782495754428799633:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((1396821271:ℚ)/2000000000),((3537429147:ℚ)/5000000000),((1620821271:ℚ)/5720000000),((4049429147:ℚ)/11345000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((4053577899:ℚ)/10000000000),((6182195329389146690767398248771106215085763005216588457:ℚ)/574225179201781250000000000000000000000000000000000000000),((-2359738348224757968953:ℚ)/25600000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((7043535537:ℚ)/10000000000),((713427567:ℚ)/1000000000),((8163535537:ℚ)/28837500000),((815827567:ℚ)/2288000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((481308047:ℚ)/1250000000),((355827934030886112120090091410844162536593611210054853123:ℚ)/33201829933958400000000000000000000000000000000000000000000),((-64109910773483155608441491:ℚ)/693120000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((443935239:ℚ)/625000000),((7193692353:ℚ)/10000000000),((513935239:ℚ)/1817187500),((8217692353:ℚ)/23070000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3636620561:ℚ)/10000000000),((14767300276689179103075196388243787656660813096269002438637:ℚ)/1383951806726672250000000000000000000000000000000000000000000),((-251289728272014205071119:ℚ)/2707500000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/4),((5:ℚ)/16),((179059781:ℚ)/250000000),((181327709:ℚ)/250000000),((207059781:ℚ)/732812500),((206927709:ℚ)/581500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((426253017:ℚ)/1250000000),((718092383982151984806127577878922882516368521004197507:ℚ)/67579483567942773437500000000000000000000000000000000000),((-37252247719095725113:ℚ)/400000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3610908903:ℚ)/5000000000),((7312523707:ℚ)/10000000000),((4170908903:ℚ)/14775000000),((8336523707:ℚ)/23450000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3167935297:ℚ)/10000000000),((74482818162953609976819447511553859380092721613822819243749:ℚ)/7037582984615039062500000000000000000000000000000000000000000),((-44855598386295072029291:ℚ)/480000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((7281243541:ℚ)/10000000000),((737193841:ℚ)/1000000000),((8401243541:ℚ)/29787500000),((839593841:ℚ)/2364000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2906480583:ℚ)/10000000000),((14831049965414898917294539398477639979576575715071216426869:ℚ)/1406668536014302800000000000000000000000000000000000000000000),((-21664179387780014775846153:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((7340668467:ℚ)/10000000000),((1486270497:ℚ)/2000000000),((8460668467:ℚ)/30025000000),((1691070497:ℚ)/4766000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2619863123:ℚ)/10000000000),((640788804159972194408340477454481740487457590426635256711:ℚ)/60996956149139646875000000000000000000000000000000000000000),((-65213857198982982422446571:ℚ)/693120000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((7400092601:ℚ)/10000000000),((3775089403:ℚ)/5000000000),((8520092601:ℚ)/30500000000),((4287089403:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2298683719:ℚ)/10000000000),((426975401996104418112244463919689815824715443773055824509:ℚ)/40287350745756250000000000000000000000000000000000000000000),((-21811813743074774390326913:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1879734643:ℚ)/2500000000),((7787824527:ℚ)/10000000000),((2159734643:ℚ)/7862500000),((8811824527:ℚ)/24400000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((3654619:ℚ)/25000000),((5692499153133697203244554988750097783115399946660946989753:ℚ)/528252881300000000000000000000000000000000000000000000000000),((-1372487594294147720742537:ℚ)/14440000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7756621807:ℚ)/10000000000),((4012730847:ℚ)/5000000000),((8876621807:ℚ)/32400000000),((4524730847:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((869597233993329561648877490469048784790150184818271692809:ℚ)/81637928901450000000000000000000000000000000000000000000000),((-1222213:ℚ)/12800000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((1998573571:ℚ)/2500000000),((9926324327:ℚ)/10000000000),((2278573571:ℚ)/10000000000),((1216702703:ℚ)/2880000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((366961691002934835192865012190981002617219672129323:ℚ)/27993600000000000000000000000000000000000000000000000),((-1222213:ℚ)/12800000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((989537893:ℚ)/1000000000),((6863668351:ℚ)/5000000000),((1101537893:ℚ)/5520000000),((7375668351:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((81390372735443686301823285356004778379:ℚ)/4875264000000000000000000000000000000000),((-1222213:ℚ)/12800000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC21
#check @N11Formalization.C450NinthGroupedC21.bound
#print axioms N11Formalization.C450NinthGroupedC21.valid0
#print axioms N11Formalization.C450NinthGroupedC21.valid1
#print axioms N11Formalization.C450NinthGroupedC21.valid2
#print axioms N11Formalization.C450NinthGroupedC21.valid3
#print axioms N11Formalization.C450NinthGroupedC21.valid4
#print axioms N11Formalization.C450NinthGroupedC21.valid5
#print axioms N11Formalization.C450NinthGroupedC21.valid6
#print axioms N11Formalization.C450NinthGroupedC21.valid7
#print axioms N11Formalization.C450NinthGroupedC21.valid8
#print axioms N11Formalization.C450NinthGroupedC21.valid9
#print axioms N11Formalization.C450NinthGroupedC21.valid10
#print axioms N11Formalization.C450NinthGroupedC21.valid11
#print axioms N11Formalization.C450NinthGroupedC21.valid12
#print axioms N11Formalization.C450NinthGroupedC21.valid13
#print axioms N11Formalization.C450NinthGroupedC21.valid14
#print axioms N11Formalization.C450NinthGroupedC21.valid15
#print axioms N11Formalization.C450NinthGroupedC21.bound
#print axioms N11Formalization.C450NinthGroupedC21.endpoint_checks
