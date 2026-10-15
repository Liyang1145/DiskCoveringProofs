import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((11:ℚ)/16),((3:ℚ)/4),((5248983653:ℚ)/10000000000),((1396161989:ℚ)/2500000000),((76298820183:ℚ)/103000000000),((5388485967:ℚ)/6200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((4042004603:ℚ)/5000000000),((-526356350631267391460514228900566276649681:ℚ)/1580263595000000000000000000000000000000000),((-431117549930281853694040641:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5488380563:ℚ)/10000000000),((5824133581:ℚ)/10000000000),((26310728731:ℚ)/35600000000),((22272400743:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7638831937:ℚ)/10000000000),((-70483730129171598829993330984820334985026876966762465605789:ℚ)/211315687670898437500000000000000000000000000000000000000000),((-6793509158182495989103980881:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((5727640981:ℚ)/10000000000),((5943823709:ℚ)/10000000000),((81564050791:ℚ)/108700000000),((7543823709:ℚ)/8900000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3586091937:ℚ)/5000000000),((-1792769804646616920563088793756324180621311414352353149958287:ℚ)/5206059477256250000000000000000000000000000000000000000000000),((-6740008031555165072652988401:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((5847224543:ℚ)/10000000000),((1515870291:ℚ)/2500000000),((82879469973:ℚ)/110600000000),((5747610873:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6929393973:ℚ)/10000000000),((-263132782173494475833452439574632939865725425182286382289:ℚ)/764439115927028656005859375000000000000000000000000000000),((-417851872409997251987856401:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((5966779173:ℚ)/10000000000),((6183107627:ℚ)/10000000000),((84194570903:ℚ)/112500000000),((23349322881:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((834918361:ℚ)/1250000000),((-25367032830412328942323613615007599155303410645611661:ℚ)/73727145385742187500000000000000000000000000000000000),((-6630374886714862544088336609:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((3043153179:ℚ)/5000000000),((1260540933:ℚ)/2000000000),((42754684969:ℚ)/57200000000),((1580540933:ℚ)/1875000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((6421168579:ℚ)/10000000000),((-10731001692873750776343062871874068658258034606074782653:ℚ)/31202697753906250000000000000000000000000000000000000000),((-262969710688065875187199169:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3102903741:ℚ)/5000000000),((636249261:ℚ)/1000000000),((43411941151:ℚ)/57675000000),((2388747783:ℚ)/2860000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6153809143:ℚ)/10000000000),((-3531881362897636468809719846684594059029116339312117503:ℚ)/10132394389025390625000000000000000000000000000000000000),((-65458478004811820261850641:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3132774339:ℚ)/5000000000),((6422273739:ℚ)/10000000000),((43740517729:ℚ)/58150000000),((8022273739:ℚ)/9612500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3008148693:ℚ)/5000000000),((-2616226924588449366437539786819259469915974321633031795663353:ℚ)/7508419090313977050781250000000000000000000000000000000000000),((-6517233555296589706367124641:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((6325283837:ℚ)/10000000000),((6482048221:ℚ)/10000000000),((88138122207:ℚ)/117250000000),((24246144663:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1175197699:ℚ)/2000000000),((-11769183664791259989901280176481451263916417359636688888178341:ℚ)/33789741783971386718750000000000000000000000000000000000000000),((-6488400025919162172380715761:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1596253277:ℚ)/2500000000),((6541816217:ℚ)/10000000000),((7399595349:ℚ)/9850000000),((24425448651:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((35829211:ℚ)/62500000),((-75964525606754065333930597097862879450327953657609641275639:ℚ)/218179035981369018554687500000000000000000000000000000000000),((-6459347207999663715306551769:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6444736633:ℚ)/10000000000),((6661333377:ℚ)/10000000000),((89452102963:ℚ)/120100000000),((8261333377:ℚ)/9850000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5586118471:ℚ)/10000000000),((-739727434814938526889936089647550419204673498509048860253531:ℚ)/2153846418080664062500000000000000000000000000000000000000000),((-6400583686033242104905349609:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((6564167001:ℚ)/10000000000),((6780826417:ℚ)/10000000000),((90765837011:ℚ)/122000000000),((25142479251:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2641093733:ℚ)/5000000000),((-216097839121087479464272118584625781630153301790007346064857:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-6340942952183651310007434569:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6683576001:ℚ)/10000000000),((3509872281:ℚ)/5000000000),((2488630703:ℚ)/3400000000),((12929616843:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((496158291:ℚ)/1000000000),((-535559764605517344868458108148138706172018949096111156409:ℚ)/1601501684570312500000000000000000000000000000000000000000),((-1554757427795611428013368281:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((432645863:ℚ)/625000000),((7258578841:ℚ)/10000000000),((657678277:ℚ)/900000000),((1563278619:ℚ)/1850000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((42549773:ℚ)/100000000),((-9658355211041560537046423889787909471213329628848583:ℚ)/28877343750000000000000000000000000000000000000000000),((-6093607231657029060623767001:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7161017303:ℚ)/10000000000),((183339143:ℚ)/200000000),((97331190333:ℚ)/160000000000),((215339143:ℚ)/216000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((683085129:ℚ)/2000000000),((-32563138029585538905002646161857117811791151527:ℚ)/145800000000000000000000000000000000000000000000),((-409151291:ℚ)/1024000000)⟩
theorem valid14 : Valid source31 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((2267112557:ℚ)/2500000000),((1297676609:ℚ)/1000000000),((9859412709:ℚ)/18400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-29839376430956142608769129:ℚ)/169280000000000000000000000),((-409151291:ℚ)/1024000000)⟩
theorem valid15 : Valid source31 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet15 valid15
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
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC28
#check @N11Formalization.C450Source31GroupedC28.bound
#print axioms N11Formalization.C450Source31GroupedC28.valid0
#print axioms N11Formalization.C450Source31GroupedC28.valid1
#print axioms N11Formalization.C450Source31GroupedC28.valid2
#print axioms N11Formalization.C450Source31GroupedC28.valid3
#print axioms N11Formalization.C450Source31GroupedC28.valid4
#print axioms N11Formalization.C450Source31GroupedC28.valid5
#print axioms N11Formalization.C450Source31GroupedC28.valid6
#print axioms N11Formalization.C450Source31GroupedC28.valid7
#print axioms N11Formalization.C450Source31GroupedC28.valid8
#print axioms N11Formalization.C450Source31GroupedC28.valid9
#print axioms N11Formalization.C450Source31GroupedC28.valid10
#print axioms N11Formalization.C450Source31GroupedC28.valid11
#print axioms N11Formalization.C450Source31GroupedC28.valid12
#print axioms N11Formalization.C450Source31GroupedC28.valid13
#print axioms N11Formalization.C450Source31GroupedC28.valid14
#print axioms N11Formalization.C450Source31GroupedC28.valid15
#print axioms N11Formalization.C450Source31GroupedC28.bound
#print axioms N11Formalization.C450Source31GroupedC28.endpoint_checks
