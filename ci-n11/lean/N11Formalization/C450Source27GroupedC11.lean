import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6439298203:ℚ)/10000000000),((844362051:ℚ)/1250000000),((-1533086153:ℚ)/6200000000),((-3111298203:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1119921049:ℚ)/2000000000),((342614935418941955391892702624617283260579502845548558659:ℚ)/1693726850000000000000000000000000000000000000000000000000),((-58050115133266578344770319:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((417470583:ℚ)/625000000),((6874976029:ℚ)/10000000000),((-12624928087:ℚ)/51500000000),((-209470583:ℚ)/1311250000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((621594533:ℚ)/1250000000),((71786243682985567193543527932914263833024502881607703:ℚ)/362838827047729492187500000000000000000000000000000000),((-1131381515636740904974597:ℚ)/34656000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1699892367:ℚ)/2500000000),((1386999529:ℚ)/2000000000),((-2560998587:ℚ)/10490000000),((-29927323:ℚ)/182500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1157703897:ℚ)/2500000000),((7801937473038470362318612804092347262248427081437381:ℚ)/39851448535156250000000000000000000000000000000000000),((-21737409048868026161718997:ℚ)/554496000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((1714892973:ℚ)/2500000000),((6995007573:ℚ)/10000000000),((-12985022719:ℚ)/52925000000),((-882892973:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2225411347:ℚ)/5000000000),((10955746368559958016812438040037259710949846894890388207:ℚ)/55965726487500000000000000000000000000000000000000000000),((-23561700492771321919361917:ℚ)/554496000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((345978149:ℚ)/500000000),((7055006127:ℚ)/10000000000),((-13165018381:ℚ)/53400000000),((-179578149:ℚ)/1077500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4263801207:ℚ)/10000000000),((532078554916630101734734395345247069412735779624987:ℚ)/2718203048324584960937500000000000000000000000000000),((-338539030405327219438991:ℚ)/7393280000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6979543037:ℚ)/10000000000),((7114993613:ℚ)/10000000000),((-13344980839:ℚ)/53875000000),((-3651543037:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4068777063:ℚ)/10000000000),((5417708940005094583885196209464573267601409732147666921981:ℚ)/27678076589650000000000000000000000000000000000000000000000),((-145192512192833910578550879:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7039512359:ℚ)/10000000000),((1793742581:ℚ)/2500000000),((-3381227743:ℚ)/13587500000),((-3711512359:ℚ)/21930000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3864533741:ℚ)/10000000000),((129860948453202269224575168706287006564810554346839271373:ℚ)/663440074245312500000000000000000000000000000000000000000),((-154993137098549522814194871:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((709947123:ℚ)/1000000000),((7234936543:ℚ)/10000000000),((-318716503:ℚ)/1275000000),((-377147123:ℚ)/2212000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3649518387:ℚ)/10000000000),((3517133776103337059484118710797237942490847773306597:ℚ)/17968190056250000000000000000000000000000000000000000),((-4944525593827181537965117:ℚ)/88719360000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((286376797:ℚ)/400000000),((7354838591:ℚ)/10000000000),((-2009216539:ℚ)/7900000000),((-17028533:ℚ)/100000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((855423823:ℚ)/2500000000),((381108869316967062523344998065942807332584351021:ℚ)/1928710937500000000000000000000000000000000000000),((-774141572074319623879:ℚ)/13107200000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((3639643919:ℚ)/5000000000),((7474701831:ℚ)/10000000000),((-14424105493:ℚ)/56250000000),((-1975643919:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((72886167:ℚ)/250000000),((5546745173836277892294398328082264047267366817375176259:ℚ)/28072387200000000000000000000000000000000000000000000000),((-48608382014902928678055751:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((1849779527:ℚ)/2500000000),((771431951:ℚ)/1000000000),((-1514295853:ℚ)/5720000000),((-1017779527:ℚ)/5910000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2304304493:ℚ)/10000000000),((1030530635517084828577899232169479713260419150558903607:ℚ)/5124789089062500000000000000000000000000000000000000000),((-13393554857314531263035639:ℚ)/184832000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((954834139:ℚ)/1250000000),((7953803609:ℚ)/10000000000),((-15861410827:ℚ)/59100000000),((-538834139:ℚ)/3050000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((7021806236399377751226078303360836894770027131508891721:ℚ)/34933794531250000000000000000000000000000000000000000000),((-85811529:ℚ)/1024000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((984762317:ℚ)/1250000000),((8432418793:ℚ)/10000000000),((-17297256379:ℚ)/61000000000),((-7021757:ℚ)/40000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5057574300420117094793037054811145220038879838071:ℚ)/24400000000000000000000000000000000000000000000000),((-85811529:ℚ)/1024000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((2089151731:ℚ)/2500000000),((10343416501:ℚ)/10000000000),((-23030249503:ℚ)/64800000000),((-1257151731:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((20697332681353433728432324878297280556098883560251781159:ℚ)/86400000000000000000000000000000000000000000000000000000),((-85811529:ℚ)/1024000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((1026728057:ℚ)/1000000000),((1769535159:ℚ)/1250000000),((-4308605477:ℚ)/10000000000),((-693928057:ℚ)/4416000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4158108528835610017359799582933639115983082267535319:ℚ)/14950809600000000000000000000000000000000000000000000),((-85811529:ℚ)/1024000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source27 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
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
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC11
#check @N11Formalization.C450Source27GroupedC11.bound
#print axioms N11Formalization.C450Source27GroupedC11.valid0
#print axioms N11Formalization.C450Source27GroupedC11.valid1
#print axioms N11Formalization.C450Source27GroupedC11.valid2
#print axioms N11Formalization.C450Source27GroupedC11.valid3
#print axioms N11Formalization.C450Source27GroupedC11.valid4
#print axioms N11Formalization.C450Source27GroupedC11.valid5
#print axioms N11Formalization.C450Source27GroupedC11.valid6
#print axioms N11Formalization.C450Source27GroupedC11.valid7
#print axioms N11Formalization.C450Source27GroupedC11.valid8
#print axioms N11Formalization.C450Source27GroupedC11.valid9
#print axioms N11Formalization.C450Source27GroupedC11.valid10
#print axioms N11Formalization.C450Source27GroupedC11.valid11
#print axioms N11Formalization.C450Source27GroupedC11.valid12
#print axioms N11Formalization.C450Source27GroupedC11.valid13
#print axioms N11Formalization.C450Source27GroupedC11.valid14
#print axioms N11Formalization.C450Source27GroupedC11.bound
#print axioms N11Formalization.C450Source27GroupedC11.endpoint_checks
