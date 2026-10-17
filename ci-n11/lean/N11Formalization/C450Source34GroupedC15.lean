import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((1535229037:ℚ)/2500000000),((6470990911:ℚ)/10000000000),((3769009089:ℚ)/51500000000),((3744770963:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1260041503:ℚ)/2000000000),((-61418562668091974427545516042721845456575091900925738555753:ℚ)/820398942968750000000000000000000000000000000000000000000000),((-144348193554531925431219551:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6383754833:ℚ)/10000000000),((3296038483:ℚ)/5000000000),((1823961517:ℚ)/26225000000),((14736245167:ℚ)/103000000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5735725557:ℚ)/10000000000),((-21480534290711408135087510511609665507534330757809961030021:ℚ)/298979193487329101562500000000000000000000000000000000000000),((-2478688573234854547407942631:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((101641007:ℚ)/156250000),((1678269381:ℚ)/2500000000),((881730619:ℚ)/13350000000),((228358993:ℚ)/1639062500),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2717303587:ℚ)/5000000000),((-281977222672307057339220312774348000800280665566048674269243:ℚ)/4090861718625585937500000000000000000000000000000000000000000),((-625856365510457620655271:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/8),((-1:ℚ)/16),((1325240329:ℚ)/2000000000),((846693401:ℚ)/1250000000),((433306599:ℚ)/6734375000),((2898759671:ℚ)/21360000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1279478243:ℚ)/2500000000),((-255315338446082806013429602513832870013617010582829948287:ℚ)/3780001114076375961303710937500000000000000000000000000000),((-293463129733297406259999:ℚ)/1638400000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6686757177:ℚ)/10000000000),((1366799447:ℚ)/2000000000),((681200553:ℚ)/10870000000),((14433242823:ℚ)/107750000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2476391541:ℚ)/5000000000),((-98672004375494516375686695362012101889692184914815111228969:ℚ)/1491156376267393750000000000000000000000000000000000000000000),((-8073212901642450148673991173:ℚ)/44359680000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((3373645733:ℚ)/5000000000),((1378885627:ℚ)/2000000000),((39359669:ℚ)/645000000),((7186354267:ℚ)/54350000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((191300147:ℚ)/400000000),((-10705959747522444338288590666651878084741321146601408559:ℚ)/165134191083398437500000000000000000000000000000000000000),((-683420697053331573124885231:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1361561017:ℚ)/2000000000),((217338763:ℚ)/312500000),((14665891:ℚ)/246875000),((2862438983:ℚ)/21930000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4606498091:ℚ)/10000000000),((-149631740126390072418537178288581190434508859446632959:ℚ)/2355523226371407508850097656250000000000000000000000000),((-111053621973417129425478231:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((6868298587:ℚ)/10000000000),((7075611079:ℚ)/10000000000),((351598769:ℚ)/6250000000),((14251701413:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2212038607:ℚ)/5000000000),((-4220978065342383225874610981700478066002923997224966629:ℚ)/69218873977661132812500000000000000000000000000000000000),((-2819044579259096712763226351:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((6989227357:ℚ)/10000000000),((7196312957:ℚ)/10000000000),((3043687043:ℚ)/57200000000),((14130772643:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((50455711:ℚ)/125000000),((-1849668518816523924979090378308973043938723645400774008753:ℚ)/31581435600000000000000000000000000000000000000000000000000),((-2904592704075871177123375871:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3555040909:ℚ)/5000000000),((7437524049:ℚ)/10000000000),((2802475951:ℚ)/59100000000),((538843007:ℚ)/4400000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1805099093:ℚ)/5000000000),((-1189159291188019045099212909512332128448504468346174899:ℚ)/22011979687500000000000000000000000000000000000000000000),((-747582391180062829905568799:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7351582643:ℚ)/10000000000),((1535699771:ℚ)/2000000000),((512300229:ℚ)/12200000000),((13768417357:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((256383037:ℚ)/1000000000),((-21969527233291429903774082076443988400716509562898133905557:ℚ)/440445281450000000000000000000000000000000000000000000000000),((-3162378308569090634270515871:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7592828303:ℚ)/10000000000),((8159825001:ℚ)/10000000000),((2080174999:ℚ)/64800000000),((13527171697:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((108615883:ℚ)/2500000000),((-89596684378457450323561253171825565956522421071431979599541:ℚ)/2109324758400000000000000000000000000000000000000000000000000),((-3335207001313594903436326311:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((8074646533:ℚ)/10000000000),((10079032213:ℚ)/10000000000),((160967787:ℚ)/80000000000),((13045353467:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-49094959008996129784252657577750262461579255644597585615939:ℚ)/2332800000000000000000000000000000000000000000000000000000000),((-231326837:ℚ)/1024000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((9995340471:ℚ)/10000000000),((434459857:ℚ)/312500000),((-114459857:ℚ)/2500000000),((11124659529:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((234742409202257278326302132320935273:ℚ)/16000000000000000000000000000000000000),((-231326837:ℚ)/1024000000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC15
#check @N11Formalization.C450Source34GroupedC15.bound
#print axioms N11Formalization.C450Source34GroupedC15.valid0
#print axioms N11Formalization.C450Source34GroupedC15.valid1
#print axioms N11Formalization.C450Source34GroupedC15.valid2
#print axioms N11Formalization.C450Source34GroupedC15.valid3
#print axioms N11Formalization.C450Source34GroupedC15.valid4
#print axioms N11Formalization.C450Source34GroupedC15.valid5
#print axioms N11Formalization.C450Source34GroupedC15.valid6
#print axioms N11Formalization.C450Source34GroupedC15.valid7
#print axioms N11Formalization.C450Source34GroupedC15.valid8
#print axioms N11Formalization.C450Source34GroupedC15.valid9
#print axioms N11Formalization.C450Source34GroupedC15.valid10
#print axioms N11Formalization.C450Source34GroupedC15.valid11
#print axioms N11Formalization.C450Source34GroupedC15.valid12
#print axioms N11Formalization.C450Source34GroupedC15.valid13
#print axioms N11Formalization.C450Source34GroupedC15.bound
#print axioms N11Formalization.C450Source34GroupedC15.endpoint_checks
