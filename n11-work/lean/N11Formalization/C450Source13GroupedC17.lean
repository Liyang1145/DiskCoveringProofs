import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((246058569:ℚ)/400000000),((3330241171:ℚ)/5000000000),((88:ℚ)/1335),((7170241171:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3138306013:ℚ)/5000000000),((177179949449078170162505441798053210183:ℚ)/4887058636800000000000000000000000000000),((-158100776416179:ℚ)/2048000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((828473349:ℚ)/1250000000),((6898482173:ℚ)/10000000000),((176:ℚ)/2765),((14578482173:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1278413131:ℚ)/2500000000),((48817006393134175637118414800428705324265412886216565617759001:ℚ)/1396996404688080000000000000000000000000000000000000000000000000),((-10114109517654021:ℚ)/121600000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((1373175931:ℚ)/2000000000),((7017469387:ℚ)/10000000000),((352:ℚ)/5625),((14697469387:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((177260233:ℚ)/400000000),((673768948323135136714902317867146735174010848424479166459:ℚ)/19568717910000000000000000000000000000000000000000000000000),((-16763908905343099:ℚ)/194560000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((3492455507:ℚ)/5000000000),((3538480003:ℚ)/5000000000),((704:ℚ)/11345),((7378480003:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2025446107:ℚ)/5000000000),((39177070471838642514947457154422562293219064696662591899049917:ℚ)/1145372060852050781250000000000000000000000000000000000000000000),((-42636347356216403:ℚ)/486400000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((3522211573:ℚ)/5000000000),((7136448699:ℚ)/10000000000),((4:ℚ)/65),((14816448699:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1923676879:ℚ)/5000000000),((421049954818669068351973105494513360051158565027426218421:ℚ)/12338722858881250000000000000000000000000000000000000000000),((-42999613248476917:ℚ)/486400000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((3551966497:ℚ)/5000000000),((3597967757:ℚ)/5000000000),((704:ℚ)/11535),((676178887:ℚ)/5200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((454129219:ℚ)/1250000000),((2654128646669705431789858259280332049903629102770800052051:ℚ)/77953207020000000000000000000000000000000000000000000000000),((-43362865199054113:ℚ)/486400000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7163440613:ℚ)/10000000000),((3627710249:ℚ)/5000000000),((352:ℚ)/5815),((7467710249:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3405893077:ℚ)/10000000000),((146936260891210829849908138379394814301862863468293354008413:ℚ)/4324849396020850781250000000000000000000000000000000000000000),((-87452207087343077:ℚ)/972800000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),(0:ℚ),((1:ℚ)/16),((3611473029:ℚ)/5000000000),((3657451847:ℚ)/5000000000),((704:ℚ)/11725),((7497451847:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((98848949:ℚ)/312500000),((1374796832633835910547166502741096932832777867667976003252779:ℚ)/40547690140765664062500000000000000000000000000000000000000000),((-44089328618052741:ℚ)/486400000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7282449383:ℚ)/10000000000),((3687192573:ℚ)/5000000000),((176:ℚ)/2955),((7527192573:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2900938873:ℚ)/10000000000),((744224110528100554230713388275886909174780528506772415045787:ℚ)/21992446826921997070312500000000000000000000000000000000000000),((-88905081503634407:ℚ)/972800000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((3670975319:ℚ)/5000000000),((3746671493:ℚ)/5000000000),((352:ℚ)/6005),((7586671493:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2613341409:ℚ)/10000000000),((37767045255976585894623770629995301617802138369972022974758089:ℚ)/1116553983133016250000000000000000000000000000000000000000000000),((-44815740250168151:ℚ)/486400000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((3730473569:ℚ)/5000000000),((1522458867:ℚ)/2000000000),((88:ℚ)/1525),((3058458867:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((478963677:ℚ)/2500000000),((2172847605097914709384120238561124250202290933590336123117:ℚ)/64459761193210000000000000000000000000000000000000000000000),((-45542102561442401:ℚ)/486400000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7579935937:ℚ)/10000000000),((2022010139:ℚ)/2500000000),((22:ℚ)/405),((3942010139:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((5678103:ℚ)/78125000),((1969735303811939857631930965752264498590859263407650608981:ℚ)/58172747695312500000000000000000000000000000000000000000000),((-92536835730631873:ℚ)/972800000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((8055820921:ℚ)/10000000000),((9990315313:ℚ)/10000000000),((11:ℚ)/250),((17670315313:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((17515084681514885871852637953391004926132716449996679181:ℚ)/510183360000000000000000000000000000000000000000000000000),((-12208129:ℚ)/128000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((4979259203:ℚ)/5000000000),((6896491863:ℚ)/5000000000),((11:ℚ)/345),((10736491863:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4662992767769356435298413104318294754651:ℚ)/121881600000000000000000000000000000000000),((-12208129:ℚ)/128000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC17
#check @N11Formalization.C450Source13GroupedC17.bound
#print axioms N11Formalization.C450Source13GroupedC17.valid0
#print axioms N11Formalization.C450Source13GroupedC17.valid1
#print axioms N11Formalization.C450Source13GroupedC17.valid2
#print axioms N11Formalization.C450Source13GroupedC17.valid3
#print axioms N11Formalization.C450Source13GroupedC17.valid4
#print axioms N11Formalization.C450Source13GroupedC17.valid5
#print axioms N11Formalization.C450Source13GroupedC17.valid6
#print axioms N11Formalization.C450Source13GroupedC17.valid7
#print axioms N11Formalization.C450Source13GroupedC17.valid8
#print axioms N11Formalization.C450Source13GroupedC17.valid9
#print axioms N11Formalization.C450Source13GroupedC17.valid10
#print axioms N11Formalization.C450Source13GroupedC17.valid11
#print axioms N11Formalization.C450Source13GroupedC17.valid12
#print axioms N11Formalization.C450Source13GroupedC17.valid13
#print axioms N11Formalization.C450Source13GroupedC17.bound
#print axioms N11Formalization.C450Source13GroupedC17.endpoint_checks
