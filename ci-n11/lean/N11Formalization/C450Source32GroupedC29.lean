import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/4),((13:ℚ)/16),((2575107589:ℚ)/5000000000),((686047571:ℚ)/1250000000),((10125322767:ℚ)/12875000000),((11398618423:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2065551431:ℚ)/2500000000),((-1064448957985098489625744355481108137357309:ℚ)/3160527190000000000000000000000000000000000),((-894294854857382740830319:ℚ)/1805000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((5389285323:ℚ)/10000000000),((2863820493:ℚ)/5000000000),((6989285323:ℚ)/8900000000),((47149666409:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7825519521:ℚ)/10000000000),((-1790120019906665565886113499405967239080229918653431710717:ℚ)/5282892191772460937500000000000000000000000000000000000000),((-14090209297178575963375491:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((5628242703:ℚ)/10000000000),((1461806137:ℚ)/2500000000),((21684728109:ℚ)/27175000000),((23963479781:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7368956091:ℚ)/10000000000),((-29792549668393845089161744207184407398309775899484826787370819:ℚ)/84338163531551250000000000000000000000000000000000000000000000),((-3494751807883767691601971:ℚ)/7220000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((2873841423:ℚ)/5000000000),((2983389589:ℚ)/5000000000),((1574503467:ℚ)/1975000000),((48704064657:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((7131970503:ℚ)/10000000000),((-27684240820949623014637292727051679861773586119488718948669:ℚ)/78278565470927734375000000000000000000000000000000000000000),((-13866505912157138914258739:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((5867099077:ℚ)/10000000000),((6086306363:ℚ)/10000000000),((7467099077:ℚ)/9375000000),((98961982719:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3444177649:ℚ)/5000000000),((-12218714806491857136447564731701660452404440947678792723:ℚ)/34512730000000000000000000000000000000000000000000000000),((-55010819510818297840551971:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((5986492621:ℚ)/10000000000),((61460601:ℚ)/100000000),((22759477863:ℚ)/28362500000),((997387813:ℚ)/1125000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3318677741:ℚ)/5000000000),((-3300533602993144873370300297689383906185811577807107923521:ℚ)/9162976486816406250000000000000000000000000000000000000000),((-5478126732932608310259:ℚ)/11552000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((1209236249:ℚ)/2000000000),((6205807487:ℚ)/10000000000),((4587708747:ℚ)/5720000000),((100515497331:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1627203147:ℚ)/2500000000),((-537902747330202850066743703547401220248175859496978262234127:ℚ)/1492985465924631250000000000000000000000000000000000000000000),((-54550414801773362588188571:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((305293231:ℚ)/500000000),((6265548683:ℚ)/10000000000),((385293231:ℚ)/480625000),((101292132879:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6378074003:ℚ)/10000000000),((-99706350557371547287235511980906272962380144669696950421638443:ℚ)/276681916116320000000000000000000000000000000000000000000000000),((-54318261730887929625376451:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1541385719:ℚ)/2500000000),((3162641921:ℚ)/5000000000),((5824157157:ℚ)/7268750000),((51034344973:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6244998723:ℚ)/10000000000),((-1558836470682616106231254764990918187574526192059471212834907:ℚ)/4324849396020850781250000000000000000000000000000000000000000),((-13521201981212728222164619:ℚ)/28880000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((6225216141:ℚ)/10000000000),((6385013113:ℚ)/10000000000),((23475648423:ℚ)/29312500000),((102845170469:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3054715459:ℚ)/5000000000),((-116941114827147398801613689477449650339447139649981312788622731:ℚ)/324381521126125312500000000000000000000000000000000000000000000),((-53850053197854493834868971:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6284884537:ℚ)/10000000000),((3222368319:ℚ)/5000000000),((7884884537:ℚ)/9850000000),((51810788147:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5971197663:ℚ)/10000000000),((-1878647320718768930324343521871504227761998611664251166219:ℚ)/5210245635375976562500000000000000000000000000000000000000),((-13403499344646621469768299:ℚ)/28880000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((3172274091:ℚ)/5000000000),((3252227279:ℚ)/5000000000),((11916822273:ℚ)/14893750000),((52198954627:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((233204247:ℚ)/400000000),((-1585256347039859120244380220815974664357194637338890391252043117:ℚ)/4395839175044696250000000000000000000000000000000000000000000000),((-13344160071773712744747019:ℚ)/28880000000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6404207191:ℚ)/10000000000),((3282083503:ℚ)/5000000000),((24012621573:ℚ)/30025000000),((52587085539:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2842970229:ℚ)/5000000000),((-8593925297593587185851693203742735326242148083928675287867103:ℚ)/23826935995757674560546875000000000000000000000000000000000000),((-36799156345537820503571:ℚ)/80000000000000000000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((258554467:ℚ)/400000000),((3341788003:ℚ)/5000000000),((967663401:ℚ)/1220000000),((53363244039:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2769228591:ℚ)/5000000000),((-357977012534741804500150762669950958632206249139155435331843:ℚ)/1007183768643906250000000000000000000000000000000000000000000),((-13164189941141768564232131:ℚ)/28880000000000000000000000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1316631499:ℚ)/2000000000),((6802964631:ℚ)/10000000000),((1636631499:ℚ)/2065000000),((108278540203:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2616198023:ℚ)/5000000000),((-34421191415589160807730304481975326526093973951633313239542311:ℚ)/96789805472500000000000000000000000000000000000000000000000000),((-52170330156086270299021899:ℚ)/115520000000000000000000000)⟩
theorem valid14 : Valid source32 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((418902279:ℚ)/625000000),((6922333813:ℚ)/10000000000),((1556706837:ℚ)/1965625000),((109830339569:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2454599733:ℚ)/5000000000),((-46692839584130267029002436461357866832408661661203265876971:ℚ)/131228216477413330078125000000000000000000000000000000000000),((-51678691786321568615872771:ℚ)/115520000000000000000000000)⟩
theorem valid15 : Valid source32 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source32 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((136433987:ℚ)/200000000),((1790254327:ℚ)/2500000000),((168433987:ℚ)/216000000),((28233306251:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4565199737:ℚ)/10000000000),((-3269302184983924773670301774874733338896250454666561047589:ℚ)/9448834363593750000000000000000000000000000000000000000000),((-3167486528991072824905411:ℚ)/7220000000000000000000000)⟩
theorem valid16 : Valid source32 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7060179729:ℚ)/10000000000),((9068450233:ℚ)/10000000000),((25980539187:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3791731413:ℚ)/10000000000),((-1444446094030588538449314013636577849:ℚ)/6000000000000000000000000000000000000),((-27029039:ℚ)/64000000)⟩
theorem valid17 : Valid source32 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((8966338589:ℚ)/10000000000),((6438577503:ℚ)/5000000000),((10566338589:ℚ)/18400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-32863807849777027562711857:ℚ)/169280000000000000000000000),((-27029039:ℚ)/64000000)⟩
theorem valid18 : Valid source32 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source32 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC29
#check @N11Formalization.C450Source32GroupedC29.bound
#print axioms N11Formalization.C450Source32GroupedC29.valid0
#print axioms N11Formalization.C450Source32GroupedC29.valid1
#print axioms N11Formalization.C450Source32GroupedC29.valid2
#print axioms N11Formalization.C450Source32GroupedC29.valid3
#print axioms N11Formalization.C450Source32GroupedC29.valid4
#print axioms N11Formalization.C450Source32GroupedC29.valid5
#print axioms N11Formalization.C450Source32GroupedC29.valid6
#print axioms N11Formalization.C450Source32GroupedC29.valid7
#print axioms N11Formalization.C450Source32GroupedC29.valid8
#print axioms N11Formalization.C450Source32GroupedC29.valid9
#print axioms N11Formalization.C450Source32GroupedC29.valid10
#print axioms N11Formalization.C450Source32GroupedC29.valid11
#print axioms N11Formalization.C450Source32GroupedC29.valid12
#print axioms N11Formalization.C450Source32GroupedC29.valid13
#print axioms N11Formalization.C450Source32GroupedC29.valid14
#print axioms N11Formalization.C450Source32GroupedC29.valid15
#print axioms N11Formalization.C450Source32GroupedC29.valid16
#print axioms N11Formalization.C450Source32GroupedC29.valid17
#print axioms N11Formalization.C450Source32GroupedC29.valid18
#print axioms N11Formalization.C450Source32GroupedC29.bound
#print axioms N11Formalization.C450Source32GroupedC29.endpoint_checks
