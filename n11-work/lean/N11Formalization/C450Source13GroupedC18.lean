import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((765210327:ℚ)/1250000000),((3316519557:ℚ)/5000000000),((1645210327:ℚ)/13350000000),((5236519557:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3171518299:ℚ)/5000000000),((20760767556638205059688586645032749729:ℚ)/610882329600000000000000000000000000000),((-5602840397088703025619193:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6597989559:ℚ)/10000000000),((1374207397:ℚ)/2000000000),((13637989559:ℚ)/110600000000),((2142207397:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1038641357:ℚ)/2000000000),((45188466445276476680391226359457886220129961757964274489969:ℚ)/1396996404688080000000000000000000000000000000000000000000000),((-380256802157851225081630777:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6836075421:ℚ)/10000000000),((699002327:ℚ)/1000000000),((13876075421:ℚ)/112500000000),((1083002327:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2261050257:ℚ)/5000000000),((77517325513290727222080965456056870197646690744093999:ℚ)/2446089738750000000000000000000000000000000000000000000),((-391094060197437163037763697:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((3477551729:ℚ)/5000000000),((1762378359:ℚ)/2500000000),((6997551729:ℚ)/56725000000),((907459453:ℚ)/4687500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4149283871:ℚ)/10000000000),((20810800630759877256536912922112762064267420080465140928067:ℚ)/662831053733825683593750000000000000000000000000000000000000),((-99128179399909285369841097:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((1753653493:ℚ)/2500000000),((1777250421:ℚ)/2500000000),((3513653493:ℚ)/28600000000),((2737250421:ℚ)/14181250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1975273389:ℚ)/5000000000),((91306699176242748663407481571251620863562261025401672849:ℚ)/2915987238134045410156250000000000000000000000000000000000),((-24951378957215809766131233:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((1768530557:ℚ)/2500000000),((7168488061:ℚ)/10000000000),((3528530557:ℚ)/28837500000),((11008488061:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((467732169:ℚ)/1250000000),((1080171449608689582975890678252659081193073914975738772398259:ℚ)/34585239514540000000000000000000000000000000000000000000000000),((-25120713995153591248547633:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3566814141:ℚ)/5000000000),((3613986307:ℚ)/5000000000),((7086814141:ℚ)/58150000000),((5533986307:ℚ)/28837500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3521442357:ℚ)/10000000000),((16843036994877852711887618538572913601778231012083252670791:ℚ)/540606174502606347656250000000000000000000000000000000000000),((-101160200489263132265478577:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/16),((1:ℚ)/8),((7193132187:ℚ)/10000000000),((3643727693:ℚ)/5000000000),((14233132187:ℚ)/117250000000),((5563727693:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3286939239:ℚ)/10000000000),((157544947298564117327849697021378975807118738318811344071761:ℚ)/5068461267595708007812500000000000000000000000000000000000000),((-407350199819481222631135873:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((7252633997:ℚ)/10000000000),((3673468211:ℚ)/5000000000),((14292633997:ℚ)/118200000000),((5593468211:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3035079373:ℚ)/10000000000),((85261148110323201506189440576576945993458750080125867638541:ℚ)/2749055853365249633789062500000000000000000000000000000000000),((-410059619955942385537081553:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7312133763:ℚ)/10000000000),((7465893447:ℚ)/10000000000),((14352133763:ℚ)/120100000000),((3768631149:ℚ)/19700000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((690277973:ℚ)/2500000000),((428015401397204113032576661316883640285440085482815645751691:ℚ)/13784617075716250000000000000000000000000000000000000000000000),((-412769064676448282643988273:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7431127353:ℚ)/10000000000),((7584844007:ℚ)/10000000000),((14471127353:ℚ)/122000000000),((11424844007:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((422401373:ℚ)/2000000000),((31150446486250767909134983717654476467286241942617237215937:ℚ)/1007183768643906250000000000000000000000000000000000000000000),((-418188036474074267239081753:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((3775056667:ℚ)/5000000000),((8060587307:ℚ)/10000000000),((7295056667:ℚ)/64800000000),((11900587307:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((45856223:ℚ)/400000000),((14598718364045606235874556332540075297928000606047605822757:ℚ)/465381981562500000000000000000000000000000000000000000000000),((-293356739811940497260633:ℚ)/2560000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((4012993939:ℚ)/5000000000),((4981426581:ℚ)/5000000000),((7532993939:ℚ)/80000000000),((2300475527:ℚ)/10800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((9662743989900761840256090100572956581252296314236859:ℚ)/295245000000000000000000000000000000000000000000000000),((-29493027:ℚ)/256000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((248216339:ℚ)/250000000),((688275557:ℚ)/500000000),((424216339:ℚ)/5520000000),((880275557:ℚ)/4000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((575402852165457782340127849877760569:ℚ)/15235200000000000000000000000000000000),((-29493027:ℚ)/256000000)⟩
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
end N11Formalization.C450Source13GroupedC18
#check @N11Formalization.C450Source13GroupedC18.bound
#print axioms N11Formalization.C450Source13GroupedC18.valid0
#print axioms N11Formalization.C450Source13GroupedC18.valid1
#print axioms N11Formalization.C450Source13GroupedC18.valid2
#print axioms N11Formalization.C450Source13GroupedC18.valid3
#print axioms N11Formalization.C450Source13GroupedC18.valid4
#print axioms N11Formalization.C450Source13GroupedC18.valid5
#print axioms N11Formalization.C450Source13GroupedC18.valid6
#print axioms N11Formalization.C450Source13GroupedC18.valid7
#print axioms N11Formalization.C450Source13GroupedC18.valid8
#print axioms N11Formalization.C450Source13GroupedC18.valid9
#print axioms N11Formalization.C450Source13GroupedC18.valid10
#print axioms N11Formalization.C450Source13GroupedC18.valid11
#print axioms N11Formalization.C450Source13GroupedC18.valid12
#print axioms N11Formalization.C450Source13GroupedC18.valid13
#print axioms N11Formalization.C450Source13GroupedC18.bound
#print axioms N11Formalization.C450Source13GroupedC18.endpoint_checks
