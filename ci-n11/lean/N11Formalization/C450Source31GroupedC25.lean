import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/2),((9:ℚ)/16),((2722550039:ℚ)/5000000000),((2889316211:ℚ)/5000000000),((3882550039:ℚ)/6437500000),((35603845899:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7720808887:ℚ)/10000000000),((-2430412596553842167414723187449385378870164398836617886572257:ℚ)/8090949606400000000000000000000000000000000000000000000000000),((-380862893310635389013459:ℚ)/902500000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((1421396047:ℚ)/2500000000),((6018971513:ℚ)/10000000000),((2001396047:ℚ)/3337500000),((73370743617:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7255973229:ℚ)/10000000000),((-4036835261944250985661754731271788438787897446523781868722251:ℚ)/13524204010937500000000000000000000000000000000000000000000000),((-6036434918584417956907829:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1185170443:ℚ)/2000000000),((5995181:ℚ)/9765625),((1649170443:ℚ)/2717500000),((24235543:ℚ)/34765625),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((845727481:ℚ)/1250000000),((-754423472578880224881126382414294839694819059271125993:ℚ)/2482442606571316719055175781250000000000000000000000000),((-3016916215843478459367063:ℚ)/7220000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((151147811:ℚ)/250000000),((1564778061:ℚ)/2500000000),((209147811:ℚ)/345625000),((18883002549:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3254698161:ℚ)/5000000000),((-181517249784300017626110503090419571456615539487760513380223:ℚ)/599320266886790466308593750000000000000000000000000000000000),((-93785759828904065050009:ℚ)/225625000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6165926927:ℚ)/10000000000),((3189557321:ℚ)/5000000000),((2828642309:ℚ)/4687500000),((38306015889:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6244134403:ℚ)/10000000000),((-178056906940512725150738185046078130444802427955946749:ℚ)/589817163085937500000000000000000000000000000000000000),((-2984804018532457172144937:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((157147451:ℚ)/250000000),((6499074801:ℚ)/10000000000),((215147451:ℚ)/357500000),((25897224403:ℚ)/37500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2984412741:ℚ)/5000000000),((-75121476856238002788778525224422359074537792846828259872363:ℚ)/249621582031250000000000000000000000000000000000000000000000),((-5935791307460796299443741:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3202913993:ℚ)/5000000000),((6618994833:ℚ)/10000000000),((4362913993:ℚ)/7268750000),((78770953497:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5681978539:ℚ)/10000000000),((-345226421816164196873944146955781404516996925938662847536953041:ℚ)/1150601232809600000000000000000000000000000000000000000000000000),((-5900839048306950476904849:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((326285941:ℚ)/500000000),((6738876709:ℚ)/10000000000),((147428647:ℚ)/246250000),((79849890381:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((84089337:ℚ)/156250000),((-28537978492438135372143406517213688903222654862227334859689943:ℚ)/95387534255192187500000000000000000000000000000000000000000000),((-5864751827087963477451021:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1329114493:ℚ)/2000000000),((1714680569:ℚ)/2500000000),((1793114493:ℚ)/3002500000),((6744041707:ℚ)/9850000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5065625573:ℚ)/10000000000),((-642617350525951409442450388699587851496210198293357334396801:ℚ)/2153846418080664062500000000000000000000000000000000000000000),((-2913765086418830768343033:ℚ)/7220000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((6765390717:ℚ)/10000000000),((348926663:ℚ)/500000000),((9085390717:ℚ)/15250000000),((4100339967:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((147828023:ℚ)/312500000),((-1498562549792234992195145199540121359219852450792911258741:ℚ)/5035918843219531250000000000000000000000000000000000000000),((-115783491632144282834957:ℚ)/288800000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((344258763:ℚ)/500000000),((3609028927:ℚ)/5000000000),((460258763:ℚ)/786250000),((42081260343:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((874384093:ℚ)/2000000000),((-40839694609434207692365999390193958023761665611173844371657421:ℚ)/140317171595312500000000000000000000000000000000000000000000000),((-1420338448251049300566139:ℚ)/3610000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7124649429:ℚ)/10000000000),((7457462289:ℚ)/10000000000),((9444649429:ℚ)/16200000000),((86317160601:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3555537349:ℚ)/10000000000),((-213243104481318762005015411118703849214110105905355334595397:ℚ)/735476836950000000000000000000000000000000000000000000000000),((-5596725951559766989418711:ℚ)/14440000000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3682003233:ℚ)/5000000000),((1873882409:ℚ)/2000000000),((4842003233:ℚ)/10000000000),((6901647227:ℚ)/8640000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2498552667:ℚ)/10000000000),((-33224408881422934208387164279846500123461697818842403:ℚ)/149299200000000000000000000000000000000000000000000000),((-187505292723436219:ℚ)/486400000000000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((9275659523:ℚ)/10000000000),((6591693107:ℚ)/5000000000),((3865219841:ℚ)/9200000000),((68925237963:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-74458853974993046665369506785497770889211236604728585584521:ℚ)/423200000000000000000000000000000000000000000000000000000000),((-49827547:ℚ)/128000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC25
#check @N11Formalization.C450Source31GroupedC25.bound
#print axioms N11Formalization.C450Source31GroupedC25.valid0
#print axioms N11Formalization.C450Source31GroupedC25.valid1
#print axioms N11Formalization.C450Source31GroupedC25.valid2
#print axioms N11Formalization.C450Source31GroupedC25.valid3
#print axioms N11Formalization.C450Source31GroupedC25.valid4
#print axioms N11Formalization.C450Source31GroupedC25.valid5
#print axioms N11Formalization.C450Source31GroupedC25.valid6
#print axioms N11Formalization.C450Source31GroupedC25.valid7
#print axioms N11Formalization.C450Source31GroupedC25.valid8
#print axioms N11Formalization.C450Source31GroupedC25.valid9
#print axioms N11Formalization.C450Source31GroupedC25.valid10
#print axioms N11Formalization.C450Source31GroupedC25.valid11
#print axioms N11Formalization.C450Source31GroupedC25.valid12
#print axioms N11Formalization.C450Source31GroupedC25.valid13
#print axioms N11Formalization.C450Source31GroupedC25.bound
#print axioms N11Formalization.C450Source31GroupedC25.endpoint_checks
