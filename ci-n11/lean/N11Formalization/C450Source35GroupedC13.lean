import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((197167887:ℚ)/312500000),((652001631:ℚ)/1000000000),((-124001631:ℚ)/2480000000),((88496339:ℚ)/3100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((591364813:ℚ)/1000000000),((935566240610562528445462593634167:ℚ)/95331200000000000000000000000000000),((-52775105730369881357741:ℚ)/902500000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((1607730783:ℚ)/2500000000),((6641381299:ℚ)/10000000000),((-1361381299:ℚ)/25275000000),((616807651:ℚ)/25275000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((5620318049:ℚ)/10000000000),((2995687545743045442445212081763004698648313395754697:ℚ)/233598345947265625000000000000000000000000000000000000),((-3776084607192289500582221:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6552367007:ℚ)/10000000000),((3381324263:ℚ)/5000000000),((-741324263:ℚ)/12875000000),((2102898979:ℚ)/103000000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2656456527:ℚ)/5000000000),((817261975749220440210537686754507011271963367976303:ℚ)/52105283737182617187500000000000000000000000000000000),((-66832124651584318211155661:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((266948403:ℚ)/400000000),((3411623597:ℚ)/5000000000),((-771623597:ℚ)/13112500000),((69554791:ℚ)/4196000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2494391863:ℚ)/5000000000),((232467850302877916250739758049616869526828228860510757:ℚ)/14090828234863281250000000000000000000000000000000000000),((-117257962873035063207701:ℚ)/1478656000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6734345577:ℚ)/10000000000),((3441911713:ℚ)/5000000000),((-801911713:ℚ)/13231250000),((1556963269:ℚ)/105850000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1204846227:ℚ)/2500000000),((64557600959393662374191061368715110972341257884617177:ℚ)/3619283909988403320312500000000000000000000000000000000),((-76528087130334978853685981:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((1698739487:ℚ)/2500000000),((3472188921:ℚ)/5000000000),((-277396307:ℚ)/4450000000),((343781539:ℚ)/26700000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((928876107:ℚ)/2000000000),((10544537394016703650295563111743631017794762365051043:ℚ)/550757031250000000000000000000000000000000000000000000),((-4986240655585837896315341:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((3427773913:ℚ)/5000000000),((3502455517:ℚ)/5000000000),((-862455517:ℚ)/13468750000),((596678261:ℚ)/53875000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((557888151:ℚ)/1250000000),((311895507820171919877962614144945084361953313837117317:ℚ)/15270803642272949218750000000000000000000000000000000000),((-20760384631318686915642941:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((276644633:ℚ)/400000000),((3532711789:ℚ)/5000000000),((-892711789:ℚ)/13587500000),((40466101:ℚ)/4348000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2137377529:ℚ)/5000000000),((21238801510397547265906587071785815430921399701559381:ℚ)/979893114471435546875000000000000000000000000000000000),((-138101075304664922834621:ℚ)/1478656000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1395332507:ℚ)/2000000000),((890739503:ℚ)/1250000000),((-230739503:ℚ)/3426562500),((166002479:ℚ)/21930000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2039171843:ℚ)/5000000000),((4959221112473901963090208209369655113015242964947:ℚ)/216582703590393066406250000000000000000000000000000),((-9927398458679373610301:ℚ)/102400000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7037188527:ℚ)/10000000000),((7246842737:ℚ)/10000000000),((-1966842737:ℚ)/27650000000),((648434419:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((24203989:ℚ)/62500000),((488127885135867820411306554547014892878493144765369751:ℚ)/18874149218750000000000000000000000000000000000000000000),((-92886354979919753438491181:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((7158168041:ℚ)/10000000000),((1473539043:ℚ)/2000000000),((-46393227:ℚ)/625000000),((285495877:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((107081287:ℚ)/312500000),((42935537755209802821295152100662442354238498049267:ℚ)/1525878906250000000000000000000000000000000000000000),((-99498865999732933077305309:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1819738693:ℚ)/2500000000),((475574517:ℚ)/625000000),((-13234047:ℚ)/162500000),((-19216079:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2916970983:ℚ)/10000000000),((225834966346089191837301849108758330746979973543:ℚ)/6704711914062500000000000000000000000000000000000),((-6634069010652519861003461:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((7520326993:ℚ)/10000000000),((7850434411:ℚ)/10000000000),((-2570434411:ℚ)/29550000000),((-800980979:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1449252109:ℚ)/10000000000),((2024228316041851510923674915064448627021887624509571937:ℚ)/53756528906250000000000000000000000000000000000000000000),((-119559010175051136853231661:ℚ)/924160000000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((1940363109:ℚ)/2500000000),((1666449249:ℚ)/2000000000),((-610449249:ℚ)/6100000000),((-381089327:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((16835354142660516677307244508585364776877941496828969:ℚ)/354657812500000000000000000000000000000000000000000000),((-8589023:ℚ)/64000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8243052277:ℚ)/10000000000),((320403777:ℚ)/312500000),((-51801259:ℚ)/337500000),((-2969156831:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((435696877722313822387725661842815916977853762817:ℚ)/5005645751953125000000000000000000000000000000000),((-8589023:ℚ)/64000000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((158798227:ℚ)/156250000),((14077030249:ℚ)/10000000000),((-8797030249:ℚ)/40000000000),((-136394681:ℚ)/3450000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2346306784306975540808322966963360883:ℚ)/16000000000000000000000000000000000000),((-8589023:ℚ)/64000000)⟩
theorem valid15 : Valid source35 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC13
#check @N11Formalization.C450Source35GroupedC13.bound
#print axioms N11Formalization.C450Source35GroupedC13.valid0
#print axioms N11Formalization.C450Source35GroupedC13.valid1
#print axioms N11Formalization.C450Source35GroupedC13.valid2
#print axioms N11Formalization.C450Source35GroupedC13.valid3
#print axioms N11Formalization.C450Source35GroupedC13.valid4
#print axioms N11Formalization.C450Source35GroupedC13.valid5
#print axioms N11Formalization.C450Source35GroupedC13.valid6
#print axioms N11Formalization.C450Source35GroupedC13.valid7
#print axioms N11Formalization.C450Source35GroupedC13.valid8
#print axioms N11Formalization.C450Source35GroupedC13.valid9
#print axioms N11Formalization.C450Source35GroupedC13.valid10
#print axioms N11Formalization.C450Source35GroupedC13.valid11
#print axioms N11Formalization.C450Source35GroupedC13.valid12
#print axioms N11Formalization.C450Source35GroupedC13.valid13
#print axioms N11Formalization.C450Source35GroupedC13.valid14
#print axioms N11Formalization.C450Source35GroupedC13.valid15
#print axioms N11Formalization.C450Source35GroupedC13.bound
#print axioms N11Formalization.C450Source35GroupedC13.endpoint_checks
