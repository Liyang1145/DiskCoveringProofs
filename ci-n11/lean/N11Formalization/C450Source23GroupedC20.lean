import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((1480293131:ℚ)/2500000000),((3233153957:ℚ)/5000000000),((2600293131:ℚ)/8900000000),((4993153957:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6775648011:ℚ)/10000000000),((78625136770699567062615739460966678073:ℚ)/943898044000000000000000000000000000000),((-2380371202868008447596419:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6400394623:ℚ)/10000000000),((1676394917:ℚ)/2500000000),((4663026267:ℚ)/15800000000),((852131639:ℚ)/2225000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5695250339:ℚ)/10000000000),((8093469670294622472810782291508013637485480024907127257:ℚ)/107414832250976562500000000000000000000000000000000000000),((-625545887936656546097659:ℚ)/1805000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((1327957087:ℚ)/2000000000),((341258509:ℚ)/500000000),((741319029:ℚ)/2500000000),((517258509:ℚ)/1382500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5081297831:ℚ)/10000000000),((42493960351692038970404612866997478176629682395269:ℚ)/589817163085937500000000000000000000000000000000000),((-25627995634221675334411:ℚ)/72200000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((6759432393:ℚ)/10000000000),((3472366243:ℚ)/5000000000),((33718297179:ℚ)/114400000000),((581374027:ℚ)/1562500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1186918913:ℚ)/2500000000),((672444388312690328825042811200722504408972571214364353:ℚ)/9375810623168945312500000000000000000000000000000000000),((-2588613577475948875269619:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((687904923:ℚ)/1000000000),((3532133993:ℚ)/5000000000),((3407714769:ℚ)/11630000000),((5292133993:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4390919689:ℚ)/10000000000),((10035466832486518021533839748740048242450845533805801504509:ℚ)/140454252051953125000000000000000000000000000000000000000000),((-2614267926921252472728619:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6998637443:ℚ)/10000000000),((7183777991:ℚ)/10000000000),((11478637443:ℚ)/39400000000),((10703777991:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4004815889:ℚ)/10000000000),((26540766798991280249058718982143396371013917291092005364673:ℚ)/372607555684344482421875000000000000000000000000000000000000),((-10559052188159777356542411:ℚ)/28880000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7118198431:ℚ)/10000000000),((1825815931:ℚ)/2500000000),((34794595293:ℚ)/120100000000),((2705815931:ℚ)/7387500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((715968283:ℚ)/2000000000),((64566962462307831363415583769228996390399711733360631369093:ℚ)/908653957627780151367187500000000000000000000000000000000000),((-666274836226092754930491:ℚ)/1805000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((1447546701:ℚ)/2000000000),((1484545267:ℚ)/2000000000),((7030640103:ℚ)/24400000000),((2188545267:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((387500877:ℚ)/1250000000),((89301502896898632147802863846311738950326923511666877749:ℚ)/1258979710804882812500000000000000000000000000000000000000),((-430444352263299694179059:ℚ)/1155200000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((735724389:ℚ)/1000000000),((3830793213:ℚ)/5000000000),((3551173167:ℚ)/12580000000),((5590793213:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((25342889:ℚ)/100000000),((39948836981442480238910333420800056295589577011468224347171:ℚ)/548113951544189453125000000000000000000000000000000000000000),((-1141310050116103:ℚ)/3040000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((1899048781:ℚ)/2500000000),((7900366113:ℚ)/10000000000),((3019048781:ℚ)/10800000000),((11420366113:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((19777737:ℚ)/625000000),((624043258735878477624270607359482770610304301829431061:ℚ)/8577373242187500000000000000000000000000000000000000000),((-2926061284087487:ℚ)/7600000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7835060519:ℚ)/10000000000),((4904201091:ℚ)/5000000000),((36945181557:ℚ)/160000000000),((6664201091:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((38894004988474848832967352203560606701713705022303917:ℚ)/415188281250000000000000000000000000000000000000000000),((-6162569:ℚ)/16000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9743633873:ℚ)/10000000000),((6808905739:ℚ)/5000000000),((14223633873:ℚ)/73600000000),((8568905739:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((33009353594109268363141123105412543991:ℚ)/264500000000000000000000000000000000000),((-6162569:ℚ)/16000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC20
#check @N11Formalization.C450Source23GroupedC20.bound
#print axioms N11Formalization.C450Source23GroupedC20.valid0
#print axioms N11Formalization.C450Source23GroupedC20.valid1
#print axioms N11Formalization.C450Source23GroupedC20.valid2
#print axioms N11Formalization.C450Source23GroupedC20.valid3
#print axioms N11Formalization.C450Source23GroupedC20.valid4
#print axioms N11Formalization.C450Source23GroupedC20.valid5
#print axioms N11Formalization.C450Source23GroupedC20.valid6
#print axioms N11Formalization.C450Source23GroupedC20.valid7
#print axioms N11Formalization.C450Source23GroupedC20.valid8
#print axioms N11Formalization.C450Source23GroupedC20.valid9
#print axioms N11Formalization.C450Source23GroupedC20.valid10
#print axioms N11Formalization.C450Source23GroupedC20.valid11
#print axioms N11Formalization.C450Source23GroupedC20.bound
#print axioms N11Formalization.C450Source23GroupedC20.endpoint_checks
