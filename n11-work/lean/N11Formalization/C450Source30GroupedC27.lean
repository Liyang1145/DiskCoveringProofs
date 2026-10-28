import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/8),((11:ℚ)/16),((2672504069:ℚ)/5000000000),((1419463199:ℚ)/2500000000),((3568504069:ℚ)/5150000000),((20254095189:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7907806777:ℚ)/10000000000),((-10133769394448404127416118093686656475102215630581838766841:ℚ)/32624796800000000000000000000000000000000000000000000000000),((-2043913973644930103043251:ℚ)/4620800000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5584647951:ℚ)/10000000000),((5917493863:ℚ)/10000000000),((7376647951:ℚ)/10680000000),((83652432493:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7453919739:ℚ)/10000000000),((-12577145184504969641855068826329770282292745516563429370036621:ℚ)/40572612032812500000000000000000000000000000000000000000000000),((-32253715323294457765503619:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((728016697:ℚ)/1250000000),((1207451507:ℚ)/2000000000),((952016697:ℚ)/1358750000),((16993966577:ℚ)/21360000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((279072839:ℚ)/400000000),((-848293366848188431642289702057557964795181184506362441806881:ℚ)/2665502452355200000000000000000000000000000000000000000000000),((-1281728613308407650473899:ℚ)/2957312000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((742977963:ℚ)/1250000000),((1539246487:ℚ)/2500000000),((138139709:ℚ)/197500000),((21571711357:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3363982097:ℚ)/5000000000),((-3886055114654344704633383253800451777400961559928388487007:ℚ)/12231025854832458496093750000000000000000000000000000000000),((-104625770116282182118001:ℚ)/243200000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((6063481159:ℚ)/10000000000),((1569170229:ℚ)/2500000000),((7855481159:ℚ)/11250000000),((21900872519:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6471149631:ℚ)/10000000000),((-4420142574689084660520588213235865743909325471522547623:ℚ)/13934430477905273437500000000000000000000000000000000000),((-5918296192125280118444273:ℚ)/13862400000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((3091553811:ℚ)/5000000000),((1599086033:ℚ)/2500000000),((3987553811:ℚ)/5720000000),((7409982121:ℚ)/9375000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3102680969:ℚ)/5000000000),((-1235299480663373988415602087844599725974746774985172357617:ℚ)/3900337219238281250000000000000000000000000000000000000000),((-1957328298752720119305939:ℚ)/4620800000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((315135233:ℚ)/500000000),((814497147:ℚ)/1250000000),((404735233:ℚ)/581500000),((11279468617:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5929366791:ℚ)/10000000000),((-710673537671893880083218043177982829341251429192192821065273:ℚ)/2247268032831250000000000000000000000000000000000000000000000),((-1456183783738400741559377:ℚ)/3465600000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3211136867:ℚ)/5000000000),((6635581523:ℚ)/10000000000),((4107136867:ℚ)/5910000000),((91551396753:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5641638043:ℚ)/10000000000),((-90363992195641896728653308480223045396465727231409427168930169:ℚ)/286162602765576562500000000000000000000000000000000000000000000),((-30808250807720694308374379:ℚ)/73932800000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1635454053:ℚ)/2500000000),((1688789639:ℚ)/2500000000),((2083454053:ℚ)/3002500000),((7738895343:ℚ)/9850000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5340250479:ℚ)/10000000000),((-679182545019054581366189161887119880346836998370779040034637:ℚ)/2153846418080664062500000000000000000000000000000000000000000),((-1909140226697057482427971:ℚ)/4620800000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((1665333343:ℚ)/2500000000),((107417337:ℚ)/156250000),((2113333343:ℚ)/3050000000),((1471590707:ℚ)/1876562500),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1255679013:ℚ)/2500000000),((-96792486335319853729195544377914986949640451594757468751:ℚ)/307368093458223342895507812500000000000000000000000000000),((-44354345306375978985139:ℚ)/108300000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1695206603:ℚ)/2500000000),((111152161:ℚ)/156250000),((2143206603:ℚ)/3145000000),((1512673771:ℚ)/1906250000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2342861097:ℚ)/5000000000),((-1315202574481798945736222394418783393034938258459948566729:ℚ)/4282140246438980102539062500000000000000000000000000000000),((-14506241249771819309517:ℚ)/36100000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7019744557:ℚ)/10000000000),((229771143:ℚ)/312500000),((8811744557:ℚ)/12960000000),((3107482573:ℚ)/3931250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3932968811:ℚ)/10000000000),((-3239045970488840232461966767127500007730789140561918063:ℚ)/10562339685058593750000000000000000000000000000000000000),((-170740738915052863597669:ℚ)/433200000000000000000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((1814644709:ℚ)/2500000000),((2315426671:ℚ)/2500000000),((2262644709:ℚ)/4000000000),((30109693381:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3008796589:ℚ)/10000000000),((-107460297862194878540873927968183716519385321886993813:ℚ)/492075000000000000000000000000000000000000000000000000),((-46920965937037723:ℚ)/121600000000000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((1833391429:ℚ)/2000000000),((13072276503:ℚ)/10000000000),((730597143:ℚ)/1472000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-167070056475003699862791:ℚ)/1083392000000000000000000),((-49496479:ℚ)/128000000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC27
#check @N11Formalization.C450Source30GroupedC27.bound
#print axioms N11Formalization.C450Source30GroupedC27.valid0
#print axioms N11Formalization.C450Source30GroupedC27.valid1
#print axioms N11Formalization.C450Source30GroupedC27.valid2
#print axioms N11Formalization.C450Source30GroupedC27.valid3
#print axioms N11Formalization.C450Source30GroupedC27.valid4
#print axioms N11Formalization.C450Source30GroupedC27.valid5
#print axioms N11Formalization.C450Source30GroupedC27.valid6
#print axioms N11Formalization.C450Source30GroupedC27.valid7
#print axioms N11Formalization.C450Source30GroupedC27.valid8
#print axioms N11Formalization.C450Source30GroupedC27.valid9
#print axioms N11Formalization.C450Source30GroupedC27.valid10
#print axioms N11Formalization.C450Source30GroupedC27.valid11
#print axioms N11Formalization.C450Source30GroupedC27.valid12
#print axioms N11Formalization.C450Source30GroupedC27.valid13
#print axioms N11Formalization.C450Source30GroupedC27.bound
#print axioms N11Formalization.C450Source30GroupedC27.endpoint_checks
