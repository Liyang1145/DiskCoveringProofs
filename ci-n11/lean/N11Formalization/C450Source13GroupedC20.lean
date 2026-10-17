import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((6062556103:ℚ)/10000000000),((3289246633:ℚ)/5000000000),((25227668309:ℚ)/106800000000),((4249246633:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3236584139:ℚ)/5000000000),((2084003547834648070548996989105701261:ℚ)/76360291200000000000000000000000000000),((-491846409861463376493685667:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1307760113:ℚ)/2000000000),((681647547:ℚ)/1000000000),((761611477:ℚ)/3160000000),((291215849:ℚ)/890000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5348040909:ℚ)/10000000000),((413669972722715124292987856853478071101752155222999053:ℚ)/16498918233750000000000000000000000000000000000000000000),((-20464679941043480768765747:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((6776858431:ℚ)/10000000000),((6935454321:ℚ)/10000000000),((27370575293:ℚ)/112500000000),((1265064903:ℚ)/3950000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((293579367:ℚ)/625000000),((150685458307182099307317898267419880989112393236349817:ℚ)/6240024843750000000000000000000000000000000000000000000),((-521507742713138490384250643:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((215496037:ℚ)/312500000),((7054425549:ℚ)/10000000000),((866488111:ℚ)/3575000000),((2991475183:ℚ)/9375000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((135579857:ℚ)/312500000),((504617040083014132078989556243078540791857954685311286593:ℚ)/21061820983886718750000000000000000000000000000000000000000),((-514115776797773896539547:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((3507439557:ℚ)/5000000000),((3556954211:ℚ)/5000000000),((14042318671:ℚ)/57675000000),((410632201:ℚ)/1300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((987410047:ℚ)/2500000000),((28696624082365124907945842354976499247107570003954532317:ℚ)/1218018859687500000000000000000000000000000000000000000000),((-132850588592999356319520987:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7074378907:ℚ)/10000000000),((896673691:ℚ)/1250000000),((28263136721:ℚ)/116300000000),((1136673691:ℚ)/3604687500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((935233311:ℚ)/2500000000),((198363699704185160529478447743061768335472550414683919591:ℚ)/8446971476603224182128906250000000000000000000000000000000),((-533876629251621956959180187:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/16),((1:ℚ)/4),((1426775331:ℚ)/2000000000),((7232868911:ℚ)/10000000000),((812617999:ℚ)/3350000000),((9152868911:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1760247363:ℚ)/5000000000),((2421567058313580986445175280502925846760683232438226628787:ℚ)/103437985052973632812500000000000000000000000000000000000000),((-21454046290275216511112043:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((899171551:ℚ)/1250000000),((7292346611:ℚ)/10000000000),((3577514653:ℚ)/14775000000),((9212346611:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3285959937:ℚ)/10000000000),((64168932505531776979729136536349745453818470325795893534741:ℚ)/2749055853365249633789062500000000000000000000000000000000000),((-8419155319263191913140563:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((3626433107:ℚ)/5000000000),((7351822669:ℚ)/10000000000),((14399299321:ℚ)/59575000000),((9271822669:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1517028429:ℚ)/5000000000),((12790456287100493699985742726748292331398710903604443772432577:ℚ)/549479896880587031250000000000000000000000000000000000000000000),((-135325245185628479200944587:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((182808953:ℚ)/250000000),((59290377:ℚ)/80000000),((724426859:ℚ)/3002500000),((74650377:ℚ)/238300000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((138001441:ℚ)/500000000),((35403176209519773711841409163384761728484511133696087:ℚ)/1524923903728491171875000000000000000000000000000000000),((-339860175067732359410467:ℚ)/2310400000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((1842962043:ℚ)/2500000000),((3765120689:ℚ)/5000000000),((7288886129:ℚ)/30500000000),((4725120689:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1228238401:ℚ)/5000000000),((367807893334228005541700540222966414129140782575540940471:ℚ)/15737246385061035156250000000000000000000000000000000000000),((-34140740025772120144829787:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((7490822883:ℚ)/10000000000),((97101403:ℚ)/125000000),((29512468649:ℚ)/125800000000),((121101403:ℚ)/381250000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((339410509:ℚ)/2000000000),((81086782098966904991376389164115642817825170242841519:ℚ)/3425712197151184082031250000000000000000000000000000000),((-551203750743260197406761707:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7728751889:ℚ)/10000000000),((1601192261:ℚ)/2000000000),((30226255667:ℚ)/129600000000),((1985192261:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((47916579141900112608237835935832399797691507412023670771:ℚ)/2040948222536250000000000000000000000000000000000000000000),((-38486777:ℚ)/256000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((995831959:ℚ)/1250000000),((9908155949:ℚ)/10000000000),((3867495877:ℚ)/20000000000),((11828155949:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((220143859594936694150354250615169137538502481301578977:ℚ)/7971615000000000000000000000000000000000000000000000000),((-38486777:ℚ)/256000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9869194159:ℚ)/10000000000),((13710730453:ℚ)/10000000000),((36647582477:ℚ)/220800000000),((15630730453:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((524505467059315438510420654341114333641:ℚ)/15235200000000000000000000000000000000000),((-38486777:ℚ)/256000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC20
#check @N11Formalization.C450Source13GroupedC20.bound
#print axioms N11Formalization.C450Source13GroupedC20.valid0
#print axioms N11Formalization.C450Source13GroupedC20.valid1
#print axioms N11Formalization.C450Source13GroupedC20.valid2
#print axioms N11Formalization.C450Source13GroupedC20.valid3
#print axioms N11Formalization.C450Source13GroupedC20.valid4
#print axioms N11Formalization.C450Source13GroupedC20.valid5
#print axioms N11Formalization.C450Source13GroupedC20.valid6
#print axioms N11Formalization.C450Source13GroupedC20.valid7
#print axioms N11Formalization.C450Source13GroupedC20.valid8
#print axioms N11Formalization.C450Source13GroupedC20.valid9
#print axioms N11Formalization.C450Source13GroupedC20.valid10
#print axioms N11Formalization.C450Source13GroupedC20.valid11
#print axioms N11Formalization.C450Source13GroupedC20.valid12
#print axioms N11Formalization.C450Source13GroupedC20.valid13
#print axioms N11Formalization.C450Source13GroupedC20.valid14
#print axioms N11Formalization.C450Source13GroupedC20.bound
#print axioms N11Formalization.C450Source13GroupedC20.endpoint_checks
