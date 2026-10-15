import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((11:ℚ)/16),((3:ℚ)/4),((5315582829:ℚ)/10000000000),((564704713:ℚ)/1000000000),((75751411119:ℚ)/103000000000),((2142114139:ℚ)/2480000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7962123583:ℚ)/10000000000),((-966172428804497945617363544316195459605778422551927120933:ℚ)/3034106102400000000000000000000000000000000000000000000000),((-64618180941940335540589651:ℚ)/147865600000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5554732693:ℚ)/10000000000),((2943132721:ℚ)/5000000000),((78382059623:ℚ)/106800000000),((11069398163:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7511772827:ℚ)/10000000000),((-75616715057651309245119370956349907556961895344116242296343:ℚ)/237730148629760742187500000000000000000000000000000000000000),((-1590584682220902843214855939:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1448441003:ℚ)/2500000000),((3002914539:ℚ)/5000000000),((20252851033:ℚ)/27175000000),((11248743617:ℚ)/13350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1407758461:ℚ)/2000000000),((-1917367963241843783168462773392765369128349589999355720861479:ℚ)/5856816911913281250000000000000000000000000000000000000000000),((-4733539450295571255841394977:ℚ)/11089920000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((5913239151:ℚ)/10000000000),((6125364481:ℚ)/10000000000),((82325630661:ℚ)/110600000000),((22856093443:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6792282107:ℚ)/10000000000),((-83980399403982190658893527820197878570409674743245604492123:ℚ)/256851542951481628417968750000000000000000000000000000000000),((-6259624308106706816368162019:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((1206537831:ℚ)/2000000000),((6244873101:ℚ)/10000000000),((1858657349:ℚ)/2500000000),((23214619303:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3269028439:ℚ)/5000000000),((-505601982890708012034299010204952011139846775385628081:ℚ)/1548270053100585937500000000000000000000000000000000000),((-18621161372321570761156757137:ℚ)/44359680000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6152115311:ℚ)/10000000000),((6364356287:ℚ)/10000000000),((84953268421:ℚ)/114400000000),((23573068861:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((6275153067:ℚ)/10000000000),((-927411517987894823952444145660772349097122526893523382013049:ℚ)/2843345832824707031250000000000000000000000000000000000000000),((-6153674326006155307364695651:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6271518823:ℚ)/10000000000),((6424088741:ℚ)/10000000000),((86266707053:ℚ)/115350000000),((23752266223:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6002404107:ℚ)/10000000000),((-3346704444412607845944439258856856009422751207360303455009:ℚ)/10132394389025390625000000000000000000000000000000000000000),((-6126681221110296455330353899:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((158280311:ℚ)/250000000),((3241907651:ℚ)/5000000000),((2173083421:ℚ)/2907500000),((11965722953:ℚ)/14418750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((732737749:ℚ)/1250000000),((-2788035685455239155023712079599232132824765176228823693352239:ℚ)/8446971476603224182128906250000000000000000000000000000000000),((-1524871465059254871981798779:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((639090081:ℚ)/1000000000),((6543536117:ℚ)/10000000000),((8757990891:ℚ)/11725000000),((24110608351:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2859187309:ℚ)/5000000000),((-33434932156376847959778444780585785915742097740780535555441297:ℚ)/101369225351914160156250000000000000000000000000000000000000000),((-6072088236349039937032089931:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6450584063:ℚ)/10000000000),((3301625663:ℚ)/5000000000),((88236424693:ℚ)/118200000000),((1734982427:ℚ)/2093750000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2785792437:ℚ)/5000000000),((-412767733034549142832936839635383024586622173503231522787:ℚ)/1252303140199184417724609375000000000000000000000000000000),((-1511122085908382069521988451:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6510262323:ℚ)/10000000000),((336133273:ℚ)/500000000),((88892885553:ℚ)/120100000000),((1232399819:ℚ)/1477500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1084252881:ℚ)/2000000000),((-7088941210163981282361940690911066271758347856216756523637:ℚ)/21807694983066723632812500000000000000000000000000000000000),((-14971704327692646847722291:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((3314802171:ℚ)/5000000000),((342102937:ℚ)/500000000),((45102823881:ℚ)/61000000000),((1250308811:ℚ)/1501250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2554381727:ℚ)/5000000000),((-76653112280070661460058094059394145478589307246350498283:ℚ)/236058695775915527343750000000000000000000000000000000000),((-14830164945501727340064051:ℚ)/36966400000000000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6748927787:ℚ)/10000000000),((1770196639:ℚ)/2500000000),((91518205657:ℚ)/125800000000),((6430589917:ℚ)/7625000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2388911657:ℚ)/5000000000),((-260008137673742887339950556577552335540729293180300831126211:ℚ)/822170927316284179687500000000000000000000000000000000000000),((-363525430732550050405421859:ℚ)/924160000000000000000000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((1397504471:ℚ)/2000000000),((1829860461:ℚ)/2500000000),((18828549181:ℚ)/25920000000),((6609581383:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4042164813:ℚ)/10000000000),((-680697489739172501416132794414023176767618490363388441119:ℚ)/2154717295751953125000000000000000000000000000000000000000),((-1068283272763862966237744977:ℚ)/2772480000000000000000000000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((1806513079:ℚ)/2500000000),((2306674469:ℚ)/2500000000),((24191643869:ℚ)/40000000000),((8040023407:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1575000349:ℚ)/5000000000),((-137447780500555227708476598288303552179308778119125529:ℚ)/622782421875000000000000000000000000000000000000000000),((-384595241:ℚ)/1024000000)⟩
theorem valid14 : Valid source29 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((4566261123:ℚ)/5000000000),((13035195973:ℚ)/10000000000),((19622957451:ℚ)/36800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-117135602887475780561865021:ℚ)/677120000000000000000000000),((-384595241:ℚ)/1024000000)⟩
theorem valid15 : Valid source29 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC28
#check @N11Formalization.C450Source29GroupedC28.bound
#print axioms N11Formalization.C450Source29GroupedC28.valid0
#print axioms N11Formalization.C450Source29GroupedC28.valid1
#print axioms N11Formalization.C450Source29GroupedC28.valid2
#print axioms N11Formalization.C450Source29GroupedC28.valid3
#print axioms N11Formalization.C450Source29GroupedC28.valid4
#print axioms N11Formalization.C450Source29GroupedC28.valid5
#print axioms N11Formalization.C450Source29GroupedC28.valid6
#print axioms N11Formalization.C450Source29GroupedC28.valid7
#print axioms N11Formalization.C450Source29GroupedC28.valid8
#print axioms N11Formalization.C450Source29GroupedC28.valid9
#print axioms N11Formalization.C450Source29GroupedC28.valid10
#print axioms N11Formalization.C450Source29GroupedC28.valid11
#print axioms N11Formalization.C450Source29GroupedC28.valid12
#print axioms N11Formalization.C450Source29GroupedC28.valid13
#print axioms N11Formalization.C450Source29GroupedC28.valid14
#print axioms N11Formalization.C450Source29GroupedC28.valid15
#print axioms N11Formalization.C450Source29GroupedC28.bound
#print axioms N11Formalization.C450Source29GroupedC28.endpoint_checks
