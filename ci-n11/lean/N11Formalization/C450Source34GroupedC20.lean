import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/16),((1:ℚ)/4),((1434209019:ℚ)/2500000000),((3036762831:ℚ)/5000000000),((9422627057:ℚ)/25750000000),((5676762831:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7153757313:ℚ)/10000000000),((-82587492016094493417708741867891806544054397584034959209323:ℚ)/307649603613281250000000000000000000000000000000000000000000),((-54791771429007901100460103:ℚ)/173280000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((5979350697:ℚ)/10000000000),((6194564017:ℚ)/10000000000),((38418052091:ℚ)/104900000000),((11474564017:ℚ)/25750000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((6652594373:ℚ)/10000000000),((-5122831293978985076727303626761086218591075921798585283838707:ℚ)/19134668383189062500000000000000000000000000000000000000000000),((-74379043034223633409303149:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((6100467637:ℚ)/10000000000),((631551867:ℚ)/1000000000),((38781402911:ℚ)/106800000000),((1159551867:ℚ)/2622500000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((6389990647:ℚ)/10000000000),((-554420511513995442340067564430717468254092277129721558447848887:ℚ)/2094521199936300000000000000000000000000000000000000000000000000),((-2240190123932699758205647:ℚ)/6931200000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((3110748959:ℚ)/5000000000),((6436394169:ℚ)/10000000000),((19572246877:ℚ)/54350000000),((3905464723:ℚ)/8900000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((305897721:ℚ)/500000000),((-2081063812349401654146092872757134743406803147757390887829061:ℚ)/7948014960361718750000000000000000000000000000000000000000000),((-224858426208688431995178103:ℚ)/693120000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1268489251:ℚ)/2000000000),((409824671:ℚ)/625000000),((7901467753:ℚ)/22120000000),((739824671:ℚ)/1698437500),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5835127867:ℚ)/10000000000),((-970807225132449077801035515805437473582209512585764013919907:ℚ)/3746586415865868750000000000000000000000000000000000000000000),((-293822254991115590737331:ℚ)/902500000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((3231658513:ℚ)/5000000000),((3338962149:ℚ)/5000000000),((19934975539:ℚ)/56250000000),((5978962149:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5539819571:ℚ)/10000000000),((-12945241103723181539239300805508043915513479059103649445639:ℚ)/50460559129714965820312500000000000000000000000000000000000),((-56602580460045370964871823:ℚ)/173280000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((3292057149:ℚ)/5000000000),((1699646627:ℚ)/2500000000),((20116171447:ℚ)/57200000000),((3019646627:ℚ)/7031250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((209195041:ℚ)/400000000),((-8024786698982709984607433841077534629065818254650624954517:ℚ)/31581435600000000000000000000000000000000000000000000000000),((-4731729601132323258105589:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((3352420929:ℚ)/5000000000),((1729796193:ℚ)/2500000000),((20297262787:ℚ)/58150000000),((3049796193:ℚ)/7150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4902481751:ℚ)/10000000000),((-6327350654492518259202965514058913731799802307314471115079651:ℚ)/25130506944064843750000000000000000000000000000000000000000000),((-14237105392246530465071527:ℚ)/43320000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3412751617:ℚ)/5000000000),((7039722267:ℚ)/10000000000),((20478254851:ℚ)/59100000000),((12319722267:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4553832673:ℚ)/10000000000),((-61410333691607996070683140263057088020238768078174308848911:ℚ)/246055548379687500000000000000000000000000000000000000000000),((-228422408878096734197698447:ℚ)/693120000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((3473050859:ℚ)/5000000000),((7280626639:ℚ)/10000000000),((20659152577:ℚ)/61000000000),((12560626639:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2089284031:ℚ)/5000000000),((-40213143571198090622407164079991205613991880315449914443338987:ℚ)/165166980543750000000000000000000000000000000000000000000000000),((-75509354107992775778410861:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((179678053:ℚ)/250000000),((3880912397:ℚ)/5000000000),((1051034159:ℚ)/3240000000),((6520912397:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3311349457:ℚ)/10000000000),((-61369710313917486298528747748323504721627940983584515661:ℚ)/263665594800000000000000000000000000000000000000000000000),((-495172155004907:ℚ)/1520000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7668531113:ℚ)/10000000000),((9680645143:ℚ)/10000000000),((43485593339:ℚ)/160000000000),((14960645143:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-3675776377669240054269265650656139368207035953255867153336947:ℚ)/18662400000000000000000000000000000000000000000000000000000000),((-43613:ℚ)/128000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((1917597741:ℚ)/2000000000),((13502605287:ℚ)/10000000000),((428208401:ℚ)/1920000000),((18782605287:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-5487083913639051866178960865983249420709911065059171:ℚ)/33177600000000000000000000000000000000000000000000000),((-43613:ℚ)/128000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC20
#check @N11Formalization.C450Source34GroupedC20.bound
#print axioms N11Formalization.C450Source34GroupedC20.valid0
#print axioms N11Formalization.C450Source34GroupedC20.valid1
#print axioms N11Formalization.C450Source34GroupedC20.valid2
#print axioms N11Formalization.C450Source34GroupedC20.valid3
#print axioms N11Formalization.C450Source34GroupedC20.valid4
#print axioms N11Formalization.C450Source34GroupedC20.valid5
#print axioms N11Formalization.C450Source34GroupedC20.valid6
#print axioms N11Formalization.C450Source34GroupedC20.valid7
#print axioms N11Formalization.C450Source34GroupedC20.valid8
#print axioms N11Formalization.C450Source34GroupedC20.valid9
#print axioms N11Formalization.C450Source34GroupedC20.valid10
#print axioms N11Formalization.C450Source34GroupedC20.valid11
#print axioms N11Formalization.C450Source34GroupedC20.valid12
#print axioms N11Formalization.C450Source34GroupedC20.bound
#print axioms N11Formalization.C450Source34GroupedC20.endpoint_checks
