import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((3062034871:ℚ)/5000000000),((3312917891:ℚ)/5000000000),((3702034871:ℚ)/17800000000),((3872917891:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3168867271:ℚ)/5000000000),((36639680155538263487525531338236850729:ℚ)/3775592176000000000000000000000000000000),((-225974882281647203481921907:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6599492107:ℚ)/10000000000),((6863478941:ℚ)/10000000000),((23638476321:ℚ)/110600000000),((2661159647:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5189221767:ℚ)/10000000000),((36162250352308816952927174403840982103396809042510756795637:ℚ)/4042234967268750000000000000000000000000000000000000000000000),((-931173163454980918364476523:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((854647687:ℚ)/1250000000),((6982296891:ℚ)/10000000000),((1014647687:ℚ)/4687500000),((8102296891:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4518768677:ℚ)/10000000000),((1465757802950940772470604898827602732693170022114019261:ℚ)/169867342968750000000000000000000000000000000000000000000),((-14763639176913343708412563:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((6956021387:ℚ)/10000000000),((1760426253:ℚ)/2500000000),((24708064161:ℚ)/113450000000),((2040426253:ℚ)/7031250000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4146286751:ℚ)/10000000000),((94891119601002982986678163085028107242182891690852230582141:ℚ)/11185274031758308410644531250000000000000000000000000000000000),((-951738544784461652704845163:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((3507720101:ℚ)/5000000000),((3550556291:ℚ)/5000000000),((12443160303:ℚ)/57200000000),((4110556291:ℚ)/14181250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((394772103:ℚ)/1000000000),((18953846150957914000674489202126768095573624315048508313:ℚ)/2243067106256958007812500000000000000000000000000000000000),((-238793827147834137351254027:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((7074858289:ℚ)/10000000000),((1432103923:ℚ)/2000000000),((8354858289:ℚ)/38450000000),((1656103923:ℚ)/5720000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1869603383:ℚ)/5000000000),((1455671267922984545482230710198314952223226716048794430099:ℚ)/172926197572700000000000000000000000000000000000000000000000),((-958614703799429857511653667:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((1426855133:ℚ)/2000000000),((57759409:ℚ)/80000000),((5048565399:ℚ)/23260000000),((22239803:ℚ)/76900000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3518971849:ℚ)/10000000000),((1289728802163828817177284678882732782968641582640931:ℚ)/153772422969630250000000000000000000000000000000000000),((-38482269251826392763143003:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/16),((1:ℚ)/4),((1798423087:ℚ)/2500000000),((7279332123:ℚ)/10000000000),((6355269261:ℚ)/29312500000),((8399332123:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((328465521:ℚ)/1000000000),((211812803635358743890804764625972173774203774886683838116393:ℚ)/25342306337978540039062500000000000000000000000000000000000000),((-60343837001750160857281763:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1450621671:ℚ)/2000000000),((7338737623:ℚ)/10000000000),((1706621671:ℚ)/7880000000),((1208391089:ℚ)/4187500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((303299029:ℚ)/1000000000),((37091687265962960368510246093730872652082467688066511873:ℚ)/4452633387374877929687500000000000000000000000000000000000),((-107362735389432994589787:ℚ)/1638400000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((3656261851:ℚ)/5000000000),((1849535659:ℚ)/2500000000),((12888785553:ℚ)/59575000000),((2129535659:ℚ)/7387500000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((86225913:ℚ)/312500000),((356468594623705201171156636335385483626898325630285924722601:ℚ)/42928116943795861816406250000000000000000000000000000000000000),((-243099654179674635136246027:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((1474387681:ℚ)/2000000000),((3728773587:ℚ)/5000000000),((5191163043:ℚ)/24020000000),((4288773587:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1227994267:ℚ)/5000000000),((15410702352366706107125680293606207677046153835497661266441:ℚ)/1861479374668568325042724609375000000000000000000000000000000),((-39034047294249140291374147:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((46445953:ℚ)/62500000),((7576354869:ℚ)/10000000000),((163337859:ℚ)/762500000),((8696354869:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1055296683:ℚ)/5000000000),((5237871610121038365676038521437754260358571873128356232213:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-38254155650239522039043:ℚ)/577600000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7550178801:ℚ)/10000000000),((100644609:ℚ)/125000000),((8830178801:ℚ)/43200000000),((114644609:ℚ)/381250000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((572826141:ℚ)/5000000000),((34916212224624841109037702936142813963820425755892193:ℚ)/4039774145507812500000000000000000000000000000000000000),((-986224702048692499456273827:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((8025461689:ℚ)/10000000000),((4976110433:ℚ)/5000000000),((27916385067:ℚ)/160000000000),((5536110433:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((47850762518800210275590689296442669518272625166580323:ℚ)/4982259375000000000000000000000000000000000000000000000),((-68499209:ℚ)/1024000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((4963162161:ℚ)/5000000000),((13752986269:ℚ)/10000000000),((5603162161:ℚ)/36800000000),((14872986269:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((99523161502302989121849680880697836759:ℚ)/8464000000000000000000000000000000000000),((-68499209:ℚ)/1024000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC20
#check @N11Formalization.C450EighthGroupedC20.bound
#print axioms N11Formalization.C450EighthGroupedC20.valid0
#print axioms N11Formalization.C450EighthGroupedC20.valid1
#print axioms N11Formalization.C450EighthGroupedC20.valid2
#print axioms N11Formalization.C450EighthGroupedC20.valid3
#print axioms N11Formalization.C450EighthGroupedC20.valid4
#print axioms N11Formalization.C450EighthGroupedC20.valid5
#print axioms N11Formalization.C450EighthGroupedC20.valid6
#print axioms N11Formalization.C450EighthGroupedC20.valid7
#print axioms N11Formalization.C450EighthGroupedC20.valid8
#print axioms N11Formalization.C450EighthGroupedC20.valid9
#print axioms N11Formalization.C450EighthGroupedC20.valid10
#print axioms N11Formalization.C450EighthGroupedC20.valid11
#print axioms N11Formalization.C450EighthGroupedC20.valid12
#print axioms N11Formalization.C450EighthGroupedC20.valid13
#print axioms N11Formalization.C450EighthGroupedC20.valid14
#print axioms N11Formalization.C450EighthGroupedC20.bound
#print axioms N11Formalization.C450EighthGroupedC20.endpoint_checks
