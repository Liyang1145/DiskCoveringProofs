import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((3124365271:ℚ)/5000000000),((6541903851:ℚ)/10000000000),((-6825711553:ℚ)/99200000000),((235634729:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6055285089:ℚ)/10000000000),((8669238061347025522005864145080101:ℚ)/61504000000000000000000000000000000),((-32249464041671847661787779:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((405520279:ℚ)/625000000),((3390653957:ℚ)/5000000000),((-3771961871:ℚ)/51500000000),((14479721:ℚ)/3218750000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5476952829:ℚ)/10000000000),((56800277915125627007653751853753181082316459658153:ℚ)/407072529196739196777343750000000000000000000000000),((-540963169198826676176379:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6727640981:ℚ)/10000000000),((6900959449:ℚ)/10000000000),((-7902878347:ℚ)/106800000000),((-7640981:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4838383599:ℚ)/10000000000),((18438610376260165081376151201182365757845880686326648300769:ℚ)/133955308320703125000000000000000000000000000000000000000000),((-147995598973691971572915259:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((6847224543:ℚ)/10000000000),((1755144917:ℚ)/2500000000),((-2065434751:ℚ)/27175000000),((-127224543:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4488410573:ℚ)/10000000000),((1231149405473319763514737513490114691650316428439989792567:ℚ)/8975837587841796875000000000000000000000000000000000000000),((-458276595735894316967955193:ℚ)/2772480000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6966779173:ℚ)/10000000000),((357008509:ℚ)/500000000),((-431025527:ℚ)/5530000000),((-246779173:ℚ)/56250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2055504101:ℚ)/5000000000),((70399628267536196448015184633251684244373268836658207023:ℚ)/514903664588928222656250000000000000000000000000000000000),((-157528786634662213158260251:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((3543153179:ℚ)/5000000000),((3629866243:ℚ)/5000000000),((-4489598729:ℚ)/56250000000),((-16650289:ℚ)/2600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1848874367:ℚ)/5000000000),((67390500301591496633853934543613903954431815866874767:ℚ)/494325000000000000000000000000000000000000000000000000),((-40576354236831603809577179:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((3602903741:ℚ)/5000000000),((3689633993:ℚ)/5000000000),((-4668901979:ℚ)/57200000000),((-242903741:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3234876053:ℚ)/10000000000),((1493477618967412461232391115084900006868290095649143136749:ℚ)/10983613174853515625000000000000000000000000000000000000000),((-41772201563042047559224939:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((7325283837:ℚ)/10000000000),((7498777991:ℚ)/10000000000),((-9696333973:ℚ)/116300000000),((-201761279:ℚ)/19700000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2696915029:ℚ)/10000000000),((942340798367487184417326132802012697046516481284517842859:ℚ)/6946538124218750000000000000000000000000000000000000000000),((-515637003866885945068751233:ℚ)/2772480000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7444736633:ℚ)/10000000000),((1547545267:ℚ)/2000000000),((-2082635801:ℚ)/23640000000),((-724736633:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1012406339:ℚ)/5000000000),((19011278802354248736190311009779141525627009236889848371923:ℚ)/139735178125000000000000000000000000000000000000000000000000),((-176676045840087373142566691:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7683576001:ℚ)/10000000000),((8215366113:ℚ)/10000000000),((-11846098339:ℚ)/122000000000),((-963576001:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2366811382253557793144006797074580234376143786369934702369:ℚ)/17289547200000000000000000000000000000000000000000000000000),((-25335573:ℚ)/128000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((8161017303:ℚ)/10000000000),((5061701091:ℚ)/5000000000),((-8785103273:ℚ)/64800000000),((-1441017303:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((18612214556230251746132232756236465944633993383088232767489:ℚ)/129600000000000000000000000000000000000000000000000000000000),((-25335573:ℚ)/128000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((2517112557:ℚ)/2500000000),((6966405739:ℚ)/5000000000),((-14499217217:ℚ)/80000000000),((-279037519:ℚ)/9200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((292417852206038654184680272510437050539595792468539139:ℚ)/1825050000000000000000000000000000000000000000000000000),((-25335573:ℚ)/128000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC14
#check @N11Formalization.C450Source22GroupedC14.bound
#print axioms N11Formalization.C450Source22GroupedC14.valid0
#print axioms N11Formalization.C450Source22GroupedC14.valid1
#print axioms N11Formalization.C450Source22GroupedC14.valid2
#print axioms N11Formalization.C450Source22GroupedC14.valid3
#print axioms N11Formalization.C450Source22GroupedC14.valid4
#print axioms N11Formalization.C450Source22GroupedC14.valid5
#print axioms N11Formalization.C450Source22GroupedC14.valid6
#print axioms N11Formalization.C450Source22GroupedC14.valid7
#print axioms N11Formalization.C450Source22GroupedC14.valid8
#print axioms N11Formalization.C450Source22GroupedC14.valid9
#print axioms N11Formalization.C450Source22GroupedC14.valid10
#print axioms N11Formalization.C450Source22GroupedC14.valid11
#print axioms N11Formalization.C450Source22GroupedC14.bound
#print axioms N11Formalization.C450Source22GroupedC14.endpoint_checks
