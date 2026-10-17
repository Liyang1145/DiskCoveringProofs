import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6452032379:ℚ)/10000000000),((6773220151:ℚ)/10000000000),((-11679660453:ℚ)/49600000000),((-2868032379:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5567979891:ℚ)/10000000000),((57024611297496206227543031484214266392819:ℚ)/323637984256000000000000000000000000000000),((16977921384227237044598273:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6692727177:ℚ)/10000000000),((3446758181:ℚ)/5000000000),((-6020274543:ℚ)/25750000000),((-3108727177:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4936229939:ℚ)/10000000000),((79641098841599281123109590161348872292496062119537906142347:ℚ)/458693650637435913085937500000000000000000000000000000000000),((-77614160058793740528525589:ℚ)/8871936000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((851623263:ℚ)/1250000000),((3476821627:ℚ)/5000000000),((-6110464881:ℚ)/26225000000),((-403623263:ℚ)/2646250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2295569367:ℚ)/5000000000),((1193397013313080116264523315516745799515564937524336019389693:ℚ)/6920625742583691406250000000000000000000000000000000000000000),((-6173849404155274676989:ℚ)/384000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((3436547437:ℚ)/5000000000),((7013756519:ℚ)/10000000000),((-12401269557:ℚ)/52925000000),((-548182479:ℚ)/3560000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((881862623:ℚ)/2000000000),((316918134040835785484208889706870693596783477600011246220017:ℚ)/1834774262465161132812500000000000000000000000000000000000000),((-14611866833621238093328943:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((433324397:ℚ)/625000000),((3536928263:ℚ)/5000000000),((-2096928263:ℚ)/8900000000),((-209324397:ℚ)/1346875000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((527529619:ℚ)/1250000000),((424825745016739666524491093915925184392388436452961858544329:ℚ)/2455420245168750000000000000000000000000000000000000000000000),((-271054746815829694271023:ℚ)/11552000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6993272897:ℚ)/10000000000),((445871477:ℚ)/625000000),((-797614431:ℚ)/3367187500),((-3409272897:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4022882769:ℚ)/10000000000),((390870120684769488527165152306757959713594846355093572174077:ℚ)/2255438523599600791931152343750000000000000000000000000000000),((-80374552094932411005544023:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7053342857:ℚ)/10000000000),((359700909:ℚ)/500000000),((-647102727:ℚ)/2717500000),((-1156447619:ℚ)/7310000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1907980477:ℚ)/5000000000),((727139257524535730748172757528913525935380261511615071923:ℚ)/4188933316336566162109375000000000000000000000000000000000),((-91401113440120007552650503:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((3556700283:ℚ)/5000000000),((14508161:ℚ)/20000000),((-8748161:ℚ)/36550000),((-1764700283:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((449726927:ℚ)/1250000000),((377352464887188520487605013178399524034872294281327:ℚ)/2170320977994531250000000000000000000000000000000000),((-76852299782577459995210749:ℚ)/2217984000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((7173446347:ℚ)/10000000000),((7374169727:ℚ)/10000000000),((-13482509181:ℚ)/55300000000),((-3589446347:ℚ)/22500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((673251779:ℚ)/2000000000),((2149896775897020521971390147100638046812317147672054226903:ℚ)/12230448693750000000000000000000000000000000000000000000000),((-113580443679591388686798623:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((3646751681:ℚ)/5000000000),((374710687:ℚ)/500000000),((-230710687:ℚ)/937500000),((-1854751681:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((712412479:ℚ)/2500000000),((18567597373781649418650789406991130345523102824231026087:ℚ)/105309104919433593750000000000000000000000000000000000000),((-94133146579929609120447:ℚ)/2048000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7413516267:ℚ)/10000000000),((483385939:ℚ)/625000000),((-910157817:ℚ)/3575000000),((-3829516267:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2219835217:ℚ)/10000000000),((1495977207158999619216026978478893296317340119425579029039:ℚ)/8311929892309570312500000000000000000000000000000000000000),((-475334439738987572581233949:ℚ)/8871936000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((7653418429:ℚ)/10000000000),((7973980741:ℚ)/10000000000),((-5093980741:ℚ)/19700000000),((-4069418429:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((96509957189712989441940492007366085520720349993023095222227:ℚ)/533408117493750000000000000000000000000000000000000000000000),((-13419909:ℚ)/204800000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((7893168813:ℚ)/10000000000),((8453181191:ℚ)/10000000000),((-16719543573:ℚ)/61000000000),((-4309168813:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((436772771865644733690481210760417603867679647626688107138513:ℚ)/2326909907812500000000000000000000000000000000000000000000000),((-13419909:ℚ)/204800000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((1674453717:ℚ)/2000000000),((5182976977:ℚ)/5000000000),((-3742976977:ℚ)/10800000000),((-957653717:ℚ)/6400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((326688837332155269481378117916573542830649927736918599:ℚ)/1476225000000000000000000000000000000000000000000000000),((-13419909:ℚ)/204800000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10284736109:ℚ)/10000000000),((7090443301:ℚ)/5000000000),((-16951329903:ℚ)/40000000000),((-2233578703:ℚ)/14720000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2241756445187160055142253960075619121089:ℚ)/8464000000000000000000000000000000000000),((-13419909:ℚ)/204800000)⟩
theorem valid14 : Valid source29 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source29 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source29 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC11
#check @N11Formalization.C450Source29GroupedC11.bound
#print axioms N11Formalization.C450Source29GroupedC11.valid0
#print axioms N11Formalization.C450Source29GroupedC11.valid1
#print axioms N11Formalization.C450Source29GroupedC11.valid2
#print axioms N11Formalization.C450Source29GroupedC11.valid3
#print axioms N11Formalization.C450Source29GroupedC11.valid4
#print axioms N11Formalization.C450Source29GroupedC11.valid5
#print axioms N11Formalization.C450Source29GroupedC11.valid6
#print axioms N11Formalization.C450Source29GroupedC11.valid7
#print axioms N11Formalization.C450Source29GroupedC11.valid8
#print axioms N11Formalization.C450Source29GroupedC11.valid9
#print axioms N11Formalization.C450Source29GroupedC11.valid10
#print axioms N11Formalization.C450Source29GroupedC11.valid11
#print axioms N11Formalization.C450Source29GroupedC11.valid12
#print axioms N11Formalization.C450Source29GroupedC11.valid13
#print axioms N11Formalization.C450Source29GroupedC11.valid14
#print axioms N11Formalization.C450Source29GroupedC11.bound
#print axioms N11Formalization.C450Source29GroupedC11.endpoint_checks
