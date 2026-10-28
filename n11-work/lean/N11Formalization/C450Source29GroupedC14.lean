import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((3119803271:ℚ)/5000000000),((3276399781:ℚ)/5000000000),((-1189199343:ℚ)/49600000000),((1360196729:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3038172331:ℚ)/5000000000),((2192635755832592804509333756182648881:ℚ)/30505984000000000000000000000000000000),((-69865724306665715052594607:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6480867939:ℚ)/10000000000),((6673289727:ℚ)/10000000000),((-2739869181:ℚ)/103000000000),((2479132061:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5495765427:ℚ)/10000000000),((1929495624914922791619691827223354198601767258403162761:ℚ)/26677905273437500000000000000000000000000000000000000000),((-911232840089482673350882501:ℚ)/5544960000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((1650348531:ℚ)/2500000000),((3396858329:ℚ)/5000000000),((-1550574987:ℚ)/52450000000),((589651469:ℚ)/13112500000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2592086649:ℚ)/5000000000),((66216636380504332198000245277826798449795315921697733383:ℚ)/901813007031250000000000000000000000000000000000000000000),((-164101360400282388354781:ℚ)/960000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6721855739:ℚ)/10000000000),((6914083763:ℚ)/10000000000),((-1154083763:ℚ)/35600000000),((746048087:ℚ)/17800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4854722097:ℚ)/10000000000),((63018501173068151873449708408867444048284582476537855189:ℚ)/845962800000000000000000000000000000000000000000000000000),((-909138488588706396784047:ℚ)/5120000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((855282033:ℚ)/1250000000),((3517197103:ℚ)/5000000000),((-1911591309:ℚ)/54350000000),((264717967:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2251726251:ℚ)/5000000000),((4736694267943510838039890484023229688455035876877593809:ℚ)/62713159326171875000000000000000000000000000000000000000),((-15960566290982305309434109:ℚ)/86640000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((3481299467:ℚ)/5000000000),((3577325467:ℚ)/5000000000),((-2091976401:ℚ)/55300000000),((998700533:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2062375227:ℚ)/5000000000),((11556614848262693699754390589873600518115361711273073643:ℚ)/150993193750000000000000000000000000000000000000000000000),((-88207333686534928514361703:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((3541443379:ℚ)/5000000000),((7274856689:ℚ)/10000000000),((-1514856689:ℚ)/37500000000),((104284069:ℚ)/3125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3710178737:ℚ)/10000000000),((25549408403573689900407818622136206476199753137046305149:ℚ)/329589843750000000000000000000000000000000000000000000000),((-91302748536498299486766007:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((900390317:ℚ)/1250000000),((234847667:ℚ)/312500000),((-164543001:ℚ)/3575000000),((219609683:ℚ)/7150000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((649194313:ℚ)/2000000000),((5715138927337895162905560706433836779572458893056589:ℚ)/71391772460937500000000000000000000000000000000000000),((-5900582509646490735904503:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7443448241:ℚ)/10000000000),((7755218687:ℚ)/10000000000),((-1995218687:ℚ)/39400000000),((505517253:ℚ)/19700000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2033225319:ℚ)/10000000000),((93859222960341816174894758580538555694213836638289156841:ℚ)/1146805950000000000000000000000000000000000000000000000000),((-402624549058659360811637887:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7683594963:ℚ)/10000000000),((823494237:ℚ)/1000000000),((-742482711:ℚ)/12200000000),((1276405037:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((245407066807950998462268889025444613250555010185187219:ℚ)/2837262500000000000000000000000000000000000000000000000),((-5803449:ℚ)/25600000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((8163415729:ℚ)/10000000000),((10149300783:ℚ)/10000000000),((-487700087:ℚ)/4800000000),((796584271:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13735388605932640889590132855606431247686893183552609:ℚ)/129600000000000000000000000000000000000000000000000000),((-5803449:ℚ)/25600000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((5038712753:ℚ)/5000000000),((13966078659:ℚ)/10000000000),((-24618235977:ℚ)/160000000000),((-558712753:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((672046898415647329269193495911296966747279:ℚ)/4875264000000000000000000000000000000000000),((-5803449:ℚ)/25600000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC14
#check @N11Formalization.C450Source29GroupedC14.bound
#print axioms N11Formalization.C450Source29GroupedC14.valid0
#print axioms N11Formalization.C450Source29GroupedC14.valid1
#print axioms N11Formalization.C450Source29GroupedC14.valid2
#print axioms N11Formalization.C450Source29GroupedC14.valid3
#print axioms N11Formalization.C450Source29GroupedC14.valid4
#print axioms N11Formalization.C450Source29GroupedC14.valid5
#print axioms N11Formalization.C450Source29GroupedC14.valid6
#print axioms N11Formalization.C450Source29GroupedC14.valid7
#print axioms N11Formalization.C450Source29GroupedC14.valid8
#print axioms N11Formalization.C450Source29GroupedC14.valid9
#print axioms N11Formalization.C450Source29GroupedC14.valid10
#print axioms N11Formalization.C450Source29GroupedC14.valid11
#print axioms N11Formalization.C450Source29GroupedC14.bound
#print axioms N11Formalization.C450Source29GroupedC14.endpoint_checks
