import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((6087891399:ℚ)/10000000000),((25773933:ℚ)/39062500),((8007891399:ℚ)/35600000000),((32023933:ℚ)/96875000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((641768537:ℚ)/1000000000),((37103137295489381852350583146507421:ℚ)/1843550867187500000000000000000000000),((-754554276659319746254100403:ℚ)/7393280000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((656375457:ℚ)/1000000000),((6835949321:ℚ)/10000000000),((2545126371:ℚ)/11060000000),((2811983107:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5283264107:ℚ)/10000000000),((74738799057672844995805139083234838529273188669437055299511:ℚ)/4042234967268750000000000000000000000000000000000000000000000),((-7831144843836085703547747:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((6801641559:ℚ)/10000000000),((6954852373:ℚ)/10000000000),((2907213853:ℚ)/12500000000),((8554852373:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4624708447:ℚ)/10000000000),((336068567088271050286369059780393639816321377716205189:ℚ)/18874149218750000000000000000000000000000000000000000000),((-797427364720073546608284243:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((1730143807:ℚ)/2500000000),((1753575493:ℚ)/2500000000),((6630431421:ℚ)/28362500000),((2153575493:ℚ)/7031250000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4260579617:ℚ)/10000000000),((195663970243126936726012072268981412441608757535040035731323:ℚ)/11185274031758308410644531250000000000000000000000000000000000),((-50287004681238210939750947:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((27920159:ℚ)/40000000),((7073750331:ℚ)/10000000000),((106800477:ℚ)/457600000),((8673750331:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((4067125249:ℚ)/10000000000),((2032788290727746040115384921969735213442618280653300647021:ℚ)/116639489525361816406250000000000000000000000000000000000000),((-12930824091838301628643:ℚ)/118292480000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((7039502781:ℚ)/10000000000),((3566598739:ℚ)/5000000000),((8959502781:ℚ)/38450000000),((4366598739:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1932283589:ℚ)/5000000000),((46922689679445361494899832963456977107804029693918759045069:ℚ)/2701971837073437500000000000000000000000000000000000000000000),((-811762323316312580371258683:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((177474109:ℚ)/250000000),((1438528689:ℚ)/2000000000),((676422327:ℚ)/2907500000),((1758528689:ℚ)/5767500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1825693297:ℚ)/5000000000),((374257465177061391142015871882416849836271978040674959877:ℚ)/21624246980104253906250000000000000000000000000000000000000),((-509593456169547018384443:ℚ)/4620800000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/16),((1:ℚ)/4),((7158424521:ℚ)/10000000000),((362604413:ℚ)/500000000),((27235273563:ℚ)/117250000000),((442604413:ℚ)/1453750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1712798319:ℚ)/5000000000),((54649164940145246714481133910817041713355781513852990929:ℚ)/3167788292247317504882812500000000000000000000000000000000),((-818938127349038931549519123:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((7217883299:ℚ)/10000000000),((7311531951:ℚ)/10000000000),((9137883299:ℚ)/39400000000),((1273075993:ℚ)/4187500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((318451179:ℚ)/1000000000),((76579299902078373094384742056077462738120648947443417327:ℚ)/4452633387374877929687500000000000000000000000000000000000),((-822528117757630602915499003:ℚ)/7393280000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((909667591:ℚ)/1250000000),((1474194909:ℚ)/2000000000),((3449002773:ℚ)/14893750000),((1794194909:ℚ)/5910000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2924346849:ℚ)/10000000000),((376913057168956878488479914820306621899554774182695086430433:ℚ)/21979195875223481250000000000000000000000000000000000000000000),((-12908117235127199944302643:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7336796839:ℚ)/10000000000),((7430416067:ℚ)/10000000000),((27770390517:ℚ)/120100000000),((9030416067:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1319730231:ℚ)/5000000000),((254670765641608491813369637930944575706721554459895760013413:ℚ)/14891834997348546600341796875000000000000000000000000000000000),((-829712284993719600914280563:ℚ)/7393280000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((1479250333:ℚ)/2000000000),((7549295999:ℚ)/10000000000),((5589750999:ℚ)/24400000000),((9149295999:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((906547:ℚ)/3906250),((10834481655083301598586865860461235798859639167574302755369:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-33332258619661102115455867:ℚ)/295731200000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((375757879:ℚ)/500000000),((7787044069:ℚ)/10000000000),((1415273637:ℚ)/6290000000),((9387044069:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((186951773:ℚ)/1250000000),((305594437942495101143693648017723114682668223526199472059139:ℚ)/17539646449414062500000000000000000000000000000000000000000000),((-2101247572254173151976723:ℚ)/18483200000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7752955253:ℚ)/10000000000),((8024777571:ℚ)/10000000000),((9672955253:ℚ)/43200000000),((9624777571:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2448118275948252606112868054552780076678787953362171736301:ℚ)/141732515453906250000000000000000000000000000000000000000000),((-58561961:ℚ)/512000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((99884193:ℚ)/125000000),((9926245859:ℚ)/10000000000),((371652579:ℚ)/2000000000),((3842081953:ℚ)/10800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((29949689638030525057179996507733920119845600858091789:ℚ)/1476225000000000000000000000000000000000000000000000000),((-58561961:ℚ)/512000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9892497183:ℚ)/10000000000),((857998043:ℚ)/625000000),((11812497183:ℚ)/73600000000),((957998043:ℚ)/2500000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((104118902306133102765545390867580937:ℚ)/4132812500000000000000000000000000000),((-58561961:ℚ)/512000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC20
#check @N11Formalization.C450Source11GroupedC20.bound
#print axioms N11Formalization.C450Source11GroupedC20.valid0
#print axioms N11Formalization.C450Source11GroupedC20.valid1
#print axioms N11Formalization.C450Source11GroupedC20.valid2
#print axioms N11Formalization.C450Source11GroupedC20.valid3
#print axioms N11Formalization.C450Source11GroupedC20.valid4
#print axioms N11Formalization.C450Source11GroupedC20.valid5
#print axioms N11Formalization.C450Source11GroupedC20.valid6
#print axioms N11Formalization.C450Source11GroupedC20.valid7
#print axioms N11Formalization.C450Source11GroupedC20.valid8
#print axioms N11Formalization.C450Source11GroupedC20.valid9
#print axioms N11Formalization.C450Source11GroupedC20.valid10
#print axioms N11Formalization.C450Source11GroupedC20.valid11
#print axioms N11Formalization.C450Source11GroupedC20.valid12
#print axioms N11Formalization.C450Source11GroupedC20.valid13
#print axioms N11Formalization.C450Source11GroupedC20.valid14
#print axioms N11Formalization.C450Source11GroupedC20.valid15
#print axioms N11Formalization.C450Source11GroupedC20.bound
#print axioms N11Formalization.C450Source11GroupedC20.endpoint_checks
