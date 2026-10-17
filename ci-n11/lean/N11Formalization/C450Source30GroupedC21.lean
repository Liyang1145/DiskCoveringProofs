import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/4),((5:ℚ)/16),((2869397727:ℚ)/5000000000),((6065502839:ℚ)/10000000000),((5109397727:ℚ)/12875000000),((9777502839:ℚ)/19840000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1787456439:ℚ)/2500000000),((-2479259300186663869412004315271011259775009344065472333:ℚ)/13338952636718750000000000000000000000000000000000000000),((-204064911145274338292611059:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((5979992607:ℚ)/10000000000),((3153160527:ℚ)/5000000000),((10459992607:ℚ)/26700000000),((5009160527:ℚ)/10300000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3325612963:ℚ)/5000000000),((-602229225200318360603835883608003767220677421908773237:ℚ)/3304542187500000000000000000000000000000000000000000000),((-153994878270791384664704873:ℚ)/443596800000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((777615117:ℚ)/1250000000),((6426641417:ℚ)/10000000000),((1337615117:ℚ)/3396875000),((3379547139:ℚ)/7120000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3059638071:ℚ)/5000000000),((-44849507073555001412266718854200249381880975478641303:ℚ)/244973278617858886718750000000000000000000000000000000),((-208442653633392257650738931:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((126825867:ℚ)/200000000),((6546906787:ℚ)/10000000000),((30917981:ℚ)/79000000),((10258906787:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5837880639:ℚ)/10000000000),((-8735063062006916627410803229395428299427703199:ℚ)/48148339843750000000000000000000000000000000000),((-208977950374097245594005851:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((3230804457:ℚ)/5000000000),((3333560011:ℚ)/5000000000),((5470804457:ℚ)/14062500000),((5189560011:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1386022577:ℚ)/2500000000),((-452210271030776501307625211796313766251662991346849:ℚ)/2514570951461791992187500000000000000000000000000000),((-52368940128592882582426859:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((3290935291:ℚ)/5000000000),((6787283781:ℚ)/10000000000),((5530935291:ℚ)/14300000000),((10499283781:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5235783773:ℚ)/10000000000),((-3259086474375514043033484640765446745557653287458132201:ℚ)/18276293750000000000000000000000000000000000000000000000),((-629808445031168305897250657:ℚ)/1774387200000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6702081107:ℚ)/10000000000),((1381480109:ℚ)/2000000000),((11182081107:ℚ)/29075000000),((163375393:ℚ)/352000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4910191181:ℚ)/10000000000),((-27171360363727318916319514748453936620132093431878586657:ℚ)/153616967480468750000000000000000000000000000000000000000),((-8414366950592363326963899:ℚ)/23658496000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((426390191:ℚ)/625000000),((7027472633:ℚ)/10000000000),((235463397:ℚ)/615625000),((10739472633:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((912715321:ℚ)/2000000000),((-63978311971240314816081027994483520753296122116703:ℚ)/364559793472290039062500000000000000000000000000000),((-210744892599002508545578131:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((3471179413:ℚ)/5000000000),((1816872827:ℚ)/2500000000),((5711179413:ℚ)/15250000000),((914957609:ℚ)/1970000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4190687617:ℚ)/10000000000),((-3784167672120339461584318629590497267556934934295113887:ℚ)/22166113281250000000000000000000000000000000000000000000),((-13054391838110200656310091:ℚ)/36966400000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((143649213:ℚ)/200000000),((1936769793:ℚ)/2500000000),((233249213:ℚ)/648000000),((2864769793:ℚ)/6100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((832540893:ℚ)/2500000000),((-378425654878908458141926984179322355940274296223:ℚ)/2332800000000000000000000000000000000000000000000),((-3414213310969219:ℚ)/9728000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((3831099879:ℚ)/5000000000),((4830513053:ℚ)/5000000000),((6071099879:ℚ)/20000000000),((6686513053:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-6569002987108405073974008559917550497500559277887592549:ℚ)/50000000000000000000000000000000000000000000000000000000),((-74929757:ℚ)/204800000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9576604899:ℚ)/10000000000),((3369331331:ℚ)/2500000000),((14056604899:ℚ)/55200000000),((4297331331:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-3003571164824952968270147310084459755964395635655390881:ℚ)/29200800000000000000000000000000000000000000000000000000),((-74929757:ℚ)/204800000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC21
#check @N11Formalization.C450Source30GroupedC21.bound
#print axioms N11Formalization.C450Source30GroupedC21.valid0
#print axioms N11Formalization.C450Source30GroupedC21.valid1
#print axioms N11Formalization.C450Source30GroupedC21.valid2
#print axioms N11Formalization.C450Source30GroupedC21.valid3
#print axioms N11Formalization.C450Source30GroupedC21.valid4
#print axioms N11Formalization.C450Source30GroupedC21.valid5
#print axioms N11Formalization.C450Source30GroupedC21.valid6
#print axioms N11Formalization.C450Source30GroupedC21.valid7
#print axioms N11Formalization.C450Source30GroupedC21.valid8
#print axioms N11Formalization.C450Source30GroupedC21.valid9
#print axioms N11Formalization.C450Source30GroupedC21.valid10
#print axioms N11Formalization.C450Source30GroupedC21.valid11
#print axioms N11Formalization.C450Source30GroupedC21.bound
#print axioms N11Formalization.C450Source30GroupedC21.endpoint_checks
