import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((254957139:ℚ)/400000000),((1671561119:ℚ)/2500000000),((-871561119:ℚ)/4960000000),((-88557139:ℚ)/1030000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2879754421:ℚ)/5000000000),((40279079571253300985363991733929294742810888294889323:ℚ)/211715856250000000000000000000000000000000000000000000),((-93072644714550145223689:ℚ)/1108992000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((264570717:ℚ)/400000000),((1701597939:ℚ)/2500000000),((-901597939:ℚ)/5150000000),((-98170717:ℚ)/1049000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5149884499:ℚ)/10000000000),((34666742017541380890227676985355484362608906999922197:ℚ)/185773479448437500000000000000000000000000000000000000),((-108048584034364598529001:ℚ)/1108992000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((420897449:ℚ)/625000000),((6926488471:ℚ)/10000000000),((-3726488471:ℚ)/20980000000),((-53632483:ℚ)/556250000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((120483657:ℚ)/250000000),((52583025874287277403744181961357138548083003242809421:ℚ)/282101623916625976562500000000000000000000000000000000),((-94059350464070449474403:ℚ)/902500000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((6854401939:ℚ)/10000000000),((6986518721:ℚ)/10000000000),((-1262172907:ℚ)/7120000000),((-2694401939:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2233298497:ℚ)/5000000000),((7847596668585832580222034492485901441604343941210466397:ℚ)/42471922630071640014648437500000000000000000000000000000),((-25654356339540634321797763:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3457202973:ℚ)/5000000000),((7046537331:ℚ)/10000000000),((-3846537331:ℚ)/21550000000),((-1377202973:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4280178693:ℚ)/10000000000),((1248160370945543314567379984381939153402212962963641839709:ℚ)/6757342917395019531250000000000000000000000000000000000000),((-19833172391211129657902761:ℚ)/173280000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3487199393:ℚ)/5000000000),((710654461:ℚ)/1000000000),((-390654461:ℚ)/2174000000),((-1407199393:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4085847131:ℚ)/10000000000),((29909877898871430701755882515235379914310318723207192059:ℚ)/161972674376296997070312500000000000000000000000000000000),((-6808908917149254743908747:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1406876151:ℚ)/2000000000),((895817607:ℚ)/1250000000),((-495817607:ℚ)/2741250000),((-574876151:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((970602269:ℚ)/2500000000),((2228753680077796076597128108651337878865558666293798563:ℚ)/12072377694042968750000000000000000000000000000000000000),((-3363429211198473168913009:ℚ)/27724800000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((354717607:ℚ)/500000000),((7226526357:ℚ)/10000000000),((-575218051:ℚ)/3160000000),((-146717607:ℚ)/1394375000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3668344427:ℚ)/10000000000),((15442180154586019434215757931720312718297587421588591:ℚ)/83661546601200103759765625000000000000000000000000000),((-72057640056414585922747:ℚ)/577600000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((6986634:ℚ)/9765625),((728650139:ℚ)/1000000000),((-408650139:ℚ)/2231000000),((-46786144:ℚ)/439453125),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1720832657:ℚ)/5000000000),((1137440104954858227157698658171907902340560427026669:ℚ)/6163338639453286305069923400878906250000000000000000),((-338963427229887905491:ℚ)/2644042968750000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7214264249:ℚ)/10000000000),((7406421117:ℚ)/10000000000),((-4206421117:ℚ)/22500000000),((-3054264249:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3199685973:ℚ)/10000000000),((81541796910649400330763727822219040715414616816308072949:ℚ)/438631050000000000000000000000000000000000000000000000000),((-30416640037357622746568603:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7334137207:ℚ)/10000000000),((7646146173:ℚ)/10000000000),((-4446146173:ℚ)/22880000000),((-3174137207:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2652841001:ℚ)/10000000000),((120763807302683629871709276069067398468644482864105083847:ℚ)/640598636132812500000000000000000000000000000000000000000),((-32016408794879990469325947:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7573773359:ℚ)/10000000000),((7885730787:ℚ)/10000000000),((-4685730787:ℚ)/23640000000),((-3413773359:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((831006669:ℚ)/10000000000),((6581028132893668693934756468748718017350757240665162299661:ℚ)/34933794531250000000000000000000000000000000000000000000000),((-35234577954252426373803243:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((7813274751:ℚ)/10000000000),((8364528907:ℚ)/10000000000),((-5164528907:ℚ)/24400000000),((-3653274751:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((92794032285626329173027455973670745883108689549157197711:ℚ)/480265200000000000000000000000000000000000000000000000000),((-4929143:ℚ)/32000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((829192141:ℚ)/1000000000),((5138040801:ℚ)/5000000000),((-3538040801:ℚ)/12960000000),((-413192141:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2362705887591687270774311448020291923472860761603714329:ℚ)/10800000000000000000000000000000000000000000000000000000),((-4929143:ℚ)/32000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((1275376827:ℚ)/1250000000),((880599573:ℚ)/625000000),((-680599573:ℚ)/2000000000),((-755376827:ℚ)/6900000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((43303070696147815944138742902178581878477306731165367:ℚ)/171098437500000000000000000000000000000000000000000000),((-4929143:ℚ)/32000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC12
#check @N11Formalization.C450Source27GroupedC12.bound
#print axioms N11Formalization.C450Source27GroupedC12.valid0
#print axioms N11Formalization.C450Source27GroupedC12.valid1
#print axioms N11Formalization.C450Source27GroupedC12.valid2
#print axioms N11Formalization.C450Source27GroupedC12.valid3
#print axioms N11Formalization.C450Source27GroupedC12.valid4
#print axioms N11Formalization.C450Source27GroupedC12.valid5
#print axioms N11Formalization.C450Source27GroupedC12.valid6
#print axioms N11Formalization.C450Source27GroupedC12.valid7
#print axioms N11Formalization.C450Source27GroupedC12.valid8
#print axioms N11Formalization.C450Source27GroupedC12.valid9
#print axioms N11Formalization.C450Source27GroupedC12.valid10
#print axioms N11Formalization.C450Source27GroupedC12.valid11
#print axioms N11Formalization.C450Source27GroupedC12.valid12
#print axioms N11Formalization.C450Source27GroupedC12.valid13
#print axioms N11Formalization.C450Source27GroupedC12.valid14
#print axioms N11Formalization.C450Source27GroupedC12.bound
#print axioms N11Formalization.C450Source27GroupedC12.endpoint_checks
