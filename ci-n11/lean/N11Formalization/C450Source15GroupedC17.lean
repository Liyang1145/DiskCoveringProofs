import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((3069878539:ℚ)/5000000000),((6654714497:ℚ)/10000000000),((104:ℚ)/1335),((15614714497:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6302795637:ℚ)/10000000000),((770816979087521067570607494698462172763811:ℚ)/17397928747008000000000000000000000000000000),((-1520375170587131824784809403:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((1323311993:ℚ)/2000000000),((6892913483:ℚ)/10000000000),((208:ℚ)/2765),((15852913483:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2571878977:ℚ)/5000000000),((33088104965708922760256987674081928639251047885514511653398409:ℚ)/776109113715600000000000000000000000000000000000000000000000000),((-1638312354243655094963880163:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((6854868011:ℚ)/10000000000),((3505997597:ℚ)/5000000000),((416:ℚ)/5625),((7985997597:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4465177071:ℚ)/10000000000),((513433851318022771331523867608526865913527389198064223699:ℚ)/12230448693750000000000000000000000000000000000000000000000),((-424312896722949155266053203:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((871750183:ℚ)/1250000000),((3535765933:ℚ)/5000000000),((832:ℚ)/11345),((8015765933:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4087162757:ℚ)/10000000000),((26529554346901910835065529572418240483038166671567467330201813:ℚ)/636317811584472656250000000000000000000000000000000000000000000),((-431678638410151778585856563:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((879195419:ℚ)/1250000000),((7131065841:ℚ)/10000000000),((4:ℚ)/55),((16091065841:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3885249193:ℚ)/10000000000),((1837223230369947483606014987144125968937967281594495831401:ℚ)/44171167630906250000000000000000000000000000000000000000000),((-1741382710346305225325928027:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((177328053:ℚ)/250000000),((1797649297:ℚ)/2500000000),((832:ℚ)/11535),((367059027:ℚ)/2600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((734570847:ℚ)/2000000000),((673955194158699422470947887340080897401377972025710019827:ℚ)/16240251462500000000000000000000000000000000000000000000000),((-109753066544329805472139803:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7152677849:ℚ)/10000000000),((7250125971:ℚ)/10000000000),((416:ℚ)/5815),((16210125971:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((344803701:ℚ)/1000000000),((795955688997936316790188024374397974533855015399701089894833:ℚ)/19221552871203781250000000000000000000000000000000000000000000),((-1770713636846318626286202547:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),(0:ℚ),((1:ℚ)/16),((7212230611:ℚ)/10000000000),((1827413063:ℚ)/2500000000),((832:ℚ)/11725),((4067413063:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3208182321:ℚ)/10000000000),((349086667323960603507776351257117782582437957531373821982167:ℚ)/8447435445992846679687500000000000000000000000000000000000000),((-111586027789938351374731723:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((11362157:ℚ)/15625000),((7369176093:ℚ)/10000000000),((208:ℚ)/2955),((16329176093:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1474809463:ℚ)/5000000000),((36282284276637459617495218888862882753724850128696020349670517:ℚ)/879697873076879882812500000000000000000000000000000000000000000),((-1800037506461309333894067283:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((3665663763:ℚ)/5000000000),((1872054171:ℚ)/2500000000),((416:ℚ)/6005),((4112054171:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1333452611:ℚ)/5000000000),((3197147508113441683502319396959697247634102893881391522243793:ℚ)/77538471050903906250000000000000000000000000000000000000000000),((-113410465740684450221577347:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((7450413417:ℚ)/10000000000),((7607248191:ℚ)/10000000000),((104:ℚ)/1525),((16567248191:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((397465497:ℚ)/2000000000),((1655446269614399801752084999770319199478170559870287996197719:ℚ)/40287350745756250000000000000000000000000000000000000000000000),((-24261776414361111:ℚ)/194560000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7569488803:ℚ)/10000000000),((8083291411:ℚ)/10000000000),((26:ℚ)/405),((17043291411:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((896361567:ℚ)/10000000000),((769153520004944834846800027950895207133011436596519601348899:ℚ)/18615279262500000000000000000000000000000000000000000000000000),((-24650865121373149:ℚ)/194560000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((1005711823:ℚ)/1250000000),((9986470851:ℚ)/10000000000),((13:ℚ)/250),((18946470851:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((11908826722988762886956062493640031939178966024182278137:ℚ)/283435200000000000000000000000000000000000000000000000000),((-130266121:ℚ)/1024000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9949369031:ℚ)/10000000000),((13790199421:ℚ)/10000000000),((13:ℚ)/345),((22750199421:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((229271993602881823948345393340303195797423:ℚ)/4875264000000000000000000000000000000000000),((-130266121:ℚ)/1024000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC17
#check @N11Formalization.C450Source15GroupedC17.bound
#print axioms N11Formalization.C450Source15GroupedC17.valid0
#print axioms N11Formalization.C450Source15GroupedC17.valid1
#print axioms N11Formalization.C450Source15GroupedC17.valid2
#print axioms N11Formalization.C450Source15GroupedC17.valid3
#print axioms N11Formalization.C450Source15GroupedC17.valid4
#print axioms N11Formalization.C450Source15GroupedC17.valid5
#print axioms N11Formalization.C450Source15GroupedC17.valid6
#print axioms N11Formalization.C450Source15GroupedC17.valid7
#print axioms N11Formalization.C450Source15GroupedC17.valid8
#print axioms N11Formalization.C450Source15GroupedC17.valid9
#print axioms N11Formalization.C450Source15GroupedC17.valid10
#print axioms N11Formalization.C450Source15GroupedC17.valid11
#print axioms N11Formalization.C450Source15GroupedC17.valid12
#print axioms N11Formalization.C450Source15GroupedC17.valid13
#print axioms N11Formalization.C450Source15GroupedC17.bound
#print axioms N11Formalization.C450Source15GroupedC17.endpoint_checks
