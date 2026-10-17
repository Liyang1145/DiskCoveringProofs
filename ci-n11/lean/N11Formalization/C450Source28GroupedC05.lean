import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3434415053:ℚ)/5000000000),((3544120163:ℚ)/5000000000),((-8552360489:ℚ)/12400000000),((-29138565583:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2211221671:ℚ)/5000000000),((1270424120640936696054691862200260281712870900124986570960673:ℚ)/4060000894800000000000000000000000000000000000000000000000000),((1648410833752981341742989:ℚ)/3040000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1397690823:ℚ)/2000000000),((1786998709:ℚ)/2500000000),((-4320996127:ℚ)/6318750000),((-11918599053:ℚ)/20410000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4039046451:ℚ)/10000000000),((1261793395207470955652355634845036380748564792654087618317:ℚ)/4105249557232295036315917968750000000000000000000000000000),((4998583392366917893580271:ℚ)/9241600000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7048253783:ℚ)/10000000000),((7177869429:ℚ)/10000000000),((-17373608287:ℚ)/25512500000),((-60250791613:ℚ)/102525000000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((3833901817:ℚ)/10000000000),((44315877429325583146176925707562237578954759113772508147750879:ℚ)/145457916661089193725585937500000000000000000000000000000000000),((124804668226495063222730511:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((1415630127:ℚ)/2000000000),((180193557:ℚ)/250000000),((-436580671:ℚ)/640781250),((-12115931397:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((1863664453:ℚ)/5000000000),((255224056735333693000727889102259079523540017270631251953:ℚ)/837384832044192123413085937500000000000000000000000000000),((4989887127327496896681471:ℚ)/9241600000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1421609107:ℚ)/2000000000),((7237613413:ℚ)/10000000000),((-17552840239:ℚ)/25750000000),((-12181700177:ℚ)/20695000000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((1808887907:ℚ)/5000000000),((16722143341921039249781681218193305490861252363987428215883903:ℚ)/54843331061622070312500000000000000000000000000000000000000000),((4987570129967295921188151:ℚ)/9241600000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((446121157:ℚ)/625000000),((7267482853:ℚ)/10000000000),((-17642448559:ℚ)/25868750000),((-3827332727:ℚ)/6496875000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((700992491:ℚ)/2000000000),((1080633026251660557503830119497728484542881477022853142624637:ℚ)/3542757254685883712768554687500000000000000000000000000000000),((486839427529246090536951:ℚ)/902500000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7167829591:ℚ)/10000000000),((3648675311:ℚ)/5000000000),((-8866025933:ℚ)/12993750000),((-61566125501:ℚ)/104425000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((423570321:ℚ)/1250000000),((1659061746799382117691898319462840680512286575230418971179637:ℚ)/5437005989330528640747070312500000000000000000000000000000000),((6556426253096820471818901:ℚ)/12160000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((17994297:ℚ)/25000000),((1465443349:ℚ)/2000000000),((-3564330047:ℚ)/5221250000),((-154737267:ℚ)/262250000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((81704807:ℚ)/250000000),((74706833420654836430760678357378644880345585097130890376733:ℚ)/244734089450337014770507812500000000000000000000000000000000),((778205433478384895391:ℚ)/1444000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((7227606163:ℚ)/10000000000),((3678540621:ℚ)/5000000000),((-8955621863:ℚ)/13112500000),((-62223667793:ℚ)/105375000000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((157169741:ℚ)/500000000),((10192874394466421937588304046411357590086338921035962557999:ℚ)/33378776647591186523437500000000000000000000000000000000000),((124453205118706931885471031:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3628745853:ℚ)/5000000000),((923368017:ℚ)/1250000000),((-2250104051:ℚ)/3292968750),((-31276204383:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3013619511:ℚ)/10000000000),((50923387280133641683095930890531918149469144222252168913391:ℚ)/166699121432610042393207550048828125000000000000000000000000),((31098276529887161402531991:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((3643687727:ℚ)/5000000000),((1861666301:ℚ)/2500000000),((-4544998903:ℚ)/6615625000),((-31440564997:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2878192343:ℚ)/10000000000),((15138006850628437856884935839589439337770861759754975711:ℚ)/49089636731195449829101562500000000000000000000000000000),((31094696993712974554051071:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((3673568831:ℚ)/5000000000),((7506380117:ℚ)/10000000000),((-18359140351:ℚ)/26700000000),((-31769257141:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1293396927:ℚ)/5000000000),((79907169087501483173299238716125850979567954082482492793247:ℚ)/258970103982641601562500000000000000000000000000000000000000),((31064102915691023573911839:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((462930811:ℚ)/625000000),((7566089039:ℚ)/10000000000),((-18538267117:ℚ)/26937500000),((-4012238921:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1129538743:ℚ)/5000000000),((44565159262678308645759059620009666436018670534220828959357823:ℚ)/144348065510374450683593750000000000000000000000000000000000000),((484891784460496095854679:ℚ)/902500000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((373332079:ℚ)/500000000),((7685489531:ℚ)/10000000000),((-18896468593:ℚ)/27175000000),((-3242652869:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((469024509:ℚ)/2500000000),((565054709463298157009725442876168870233284190168615060884769:ℚ)/1797960800660371398925781250000000000000000000000000000000000),((309916309321869263148159:ℚ)/577600000000000000000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((7586119357:ℚ)/10000000000),((7924225189:ℚ)/10000000000),((-19612675567:ℚ)/27650000000),((-66167312927:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((604476077:ℚ)/10000000000),((67528629032113193771860462459518441265391130626968285641641:ℚ)/207823257047656250000000000000000000000000000000000000000000),((123524817596484638398832151:ℚ)/231040000000000000000000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((1956250439:ℚ)/2500000000),((8878438513:ℚ)/10000000000),((-22475315539:ℚ)/28600000000),((-17198754829:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3147026460587429517149540077430798216422297125091944877133:ℚ)/8199026550000000000000000000000000000000000000000000000000),((1710153:ℚ)/3200000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((877971481:ℚ)/1000000000),((674028273:ℚ)/625000000),((-1762084819:ℚ)/2025000000),((-7929686291:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4329327191153112256285482923817037477352587764579133:ℚ)/9730975341796875000000000000000000000000000000000000),((1710153:ℚ)/3200000)⟩
theorem valid16 : Valid source28 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((2137288093:ℚ)/2000000000),((1459149847:ℚ)/1000000000),((-3961449541:ℚ)/4000000000),((-20054169023:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((14038853548394807476575187940182196639:ℚ)/25392000000000000000000000000000000000),((1710153:ℚ)/3200000)⟩
theorem valid17 : Valid source28 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((4177:ℚ)/6400) ((843:ℚ)/1280) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((843:ℚ)/1280) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((843:ℚ)/1280) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source28 nn0 nn1 Qcell ((843:ℚ)/1280) ((267:ℚ)/400) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source28 nn0 nn1 Qcell ((843:ℚ)/1280) ((1087:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source28 nn0 nn1 Qcell ((843:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC05
#check @N11Formalization.C450Source28GroupedC05.bound
#print axioms N11Formalization.C450Source28GroupedC05.valid0
#print axioms N11Formalization.C450Source28GroupedC05.valid1
#print axioms N11Formalization.C450Source28GroupedC05.valid2
#print axioms N11Formalization.C450Source28GroupedC05.valid3
#print axioms N11Formalization.C450Source28GroupedC05.valid4
#print axioms N11Formalization.C450Source28GroupedC05.valid5
#print axioms N11Formalization.C450Source28GroupedC05.valid6
#print axioms N11Formalization.C450Source28GroupedC05.valid7
#print axioms N11Formalization.C450Source28GroupedC05.valid8
#print axioms N11Formalization.C450Source28GroupedC05.valid9
#print axioms N11Formalization.C450Source28GroupedC05.valid10
#print axioms N11Formalization.C450Source28GroupedC05.valid11
#print axioms N11Formalization.C450Source28GroupedC05.valid12
#print axioms N11Formalization.C450Source28GroupedC05.valid13
#print axioms N11Formalization.C450Source28GroupedC05.valid14
#print axioms N11Formalization.C450Source28GroupedC05.valid15
#print axioms N11Formalization.C450Source28GroupedC05.valid16
#print axioms N11Formalization.C450Source28GroupedC05.valid17
#print axioms N11Formalization.C450Source28GroupedC05.bound
#print axioms N11Formalization.C450Source28GroupedC05.endpoint_checks
