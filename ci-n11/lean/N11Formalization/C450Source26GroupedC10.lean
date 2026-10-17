import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((1623949151:ℚ)/2500000000),((1702971807:ℚ)/2500000000),((-8080802649:ℚ)/24800000000),((-2871847453:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2729021223:ℚ)/5000000000),((271138828682239804684516615907921820414116982747051572369:ℚ)/1240522595214843750000000000000000000000000000000000000000),((104593070169154030061609:ℚ)/2310400000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3367844343:ℚ)/5000000000),((3465895683:ℚ)/5000000000),((-16581269781:ℚ)/51500000000),((-6103533029:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((601946333:ℚ)/1250000000),((618551796646836728806070136963825462278045754984918062227:ℚ)/2902710616381835937500000000000000000000000000000000000000),((309615591916331354720441:ℚ)/9241600000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((8569461:ℚ)/12500000),((1747931919:ℚ)/2500000000),((-8395523433:ℚ)/26225000000),((-15708383:ℚ)/66156250),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4463041271:ℚ)/10000000000),((199829413580396381208593005272962027085642226797701:ℚ)/949157205394458770751953125000000000000000000000000),((1592347227269697089:ℚ)/57760000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((691549343:ℚ)/1000000000),((352582693:ℚ)/500000000),((-1700078851:ℚ)/5292500000),((-1274648029:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((855346001:ℚ)/2000000000),((106032389261483013418512482042495655383376264142870868137:ℚ)/503691538387500000000000000000000000000000000000000000000),((9089591522813889590441:ℚ)/369664000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((1743852037:ℚ)/2500000000),((444473137:ℚ)/625000000),((-2151311959:ℚ)/6675000000),((-3231556111:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4082503097:ℚ)/10000000000),((1117497144975821463408456271584564621173581033323247791:ℚ)/5308990328758955001831054687500000000000000000000000000),((49906684239678022217921:ℚ)/2310400000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3517656611:ℚ)/5000000000),((3585738467:ℚ)/5000000000),((-17420169269:ℚ)/53875000000),((-6552969833:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((121223961:ℚ)/312500000),((11378067529496470297321063914216862811018086872532028125903:ℚ)/54058743339160156250000000000000000000000000000000000000000),((171936319578417557410289:ℚ)/9241600000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1773802227:ℚ)/2500000000),((361568717:ℚ)/500000000),((-1762981019:ℚ)/5435000000),((-3321406681:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3665199999:ℚ)/10000000000),((306804631839688076229176499202548315119667848749166527541:ℚ)/1457754069386672973632812500000000000000000000000000000000),((36042114145176288913361:ℚ)/2310400000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((3577547727:ℚ)/5000000000),((1458252531:ℚ)/2000000000),((-2378589239:ℚ)/7310000000),((-6732643181:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((85965339:ℚ)/250000000),((952759741077098129158596099200158179304235583308120182853:ℚ)/4527141635266113281250000000000000000000000000000000000000),((116323070937769896076361:ℚ)/9241600000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7214973101:ℚ)/10000000000),((7411012949:ℚ)/10000000000),((-36517090643:ℚ)/110600000000),((-13644919303:ℚ)/56250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((799179833:ℚ)/2500000000),((1533419128667741724108266980043826225410163047623094568317:ℚ)/7208651304244995117187500000000000000000000000000000000000),((353600350123527363240209:ℚ)/36966400000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((1833675653:ℚ)/2500000000),((7530729609:ℚ)/10000000000),((-12451702421:ℚ)/37500000000),((-3501026959:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((530000397:ℚ)/2000000000),((1060009061009727032723742028541331795542374703301212183:ℚ)/4984443750000000000000000000000000000000000000000000000),((8080260957877428537281:ℚ)/2310400000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7454399197:ℚ)/10000000000),((3885034309:ℚ)/5000000000),((-19515240163:ℚ)/57200000000),((-14363197591:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1960585953:ℚ)/10000000000),((1111497658517316755680320204863750595724913732293090366873:ℚ)/5124789089062500000000000000000000000000000000000000000000),((-96276880840611887087119:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((1923425009:ℚ)/2500000000),((1601858363:ℚ)/2000000000),((-8141008541:ℚ)/23640000000),((-3770275027:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((2838101888448192792330622337397306685254615077630914354877:ℚ)/13100172949218750000000000000000000000000000000000000000000),((-644761:ℚ)/64000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((1983221873:ℚ)/2500000000),((8487432067:ℚ)/10000000000),((-44052024469:ℚ)/122000000000),((-3949665619:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((121064218354314284853882114072357137730933363911225784077:ℚ)/540298350000000000000000000000000000000000000000000000000),((-644761:ℚ)/64000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((8410962673:ℚ)/10000000000),((2079397651:ℚ)/2000000000),((-11483783557:ℚ)/25920000000),((-17232888019:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((67883530067950911787120694686461842551034110426866924609131:ℚ)/259200000000000000000000000000000000000000000000000000000000),((-644761:ℚ)/64000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((10320321277:ℚ)/10000000000),((14208171963:ℚ)/10000000000),((-84097203741:ℚ)/160000000000),((-22960963831:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1916070999668327428984767982181311365032611376340457940957:ℚ)/6307372800000000000000000000000000000000000000000000000000),((-644761:ℚ)/64000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC10
#check @N11Formalization.C450Source26GroupedC10.bound
#print axioms N11Formalization.C450Source26GroupedC10.valid0
#print axioms N11Formalization.C450Source26GroupedC10.valid1
#print axioms N11Formalization.C450Source26GroupedC10.valid2
#print axioms N11Formalization.C450Source26GroupedC10.valid3
#print axioms N11Formalization.C450Source26GroupedC10.valid4
#print axioms N11Formalization.C450Source26GroupedC10.valid5
#print axioms N11Formalization.C450Source26GroupedC10.valid6
#print axioms N11Formalization.C450Source26GroupedC10.valid7
#print axioms N11Formalization.C450Source26GroupedC10.valid8
#print axioms N11Formalization.C450Source26GroupedC10.valid9
#print axioms N11Formalization.C450Source26GroupedC10.valid10
#print axioms N11Formalization.C450Source26GroupedC10.valid11
#print axioms N11Formalization.C450Source26GroupedC10.valid12
#print axioms N11Formalization.C450Source26GroupedC10.valid13
#print axioms N11Formalization.C450Source26GroupedC10.valid14
#print axioms N11Formalization.C450Source26GroupedC10.bound
#print axioms N11Formalization.C450Source26GroupedC10.endpoint_checks
