import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5888667059:ℚ)/10000000000),((6417579241:ℚ)/10000000000),((60038003531:ℚ)/106800000000),((7185579241:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6843587129:ℚ)/10000000000),((-617457458026428541490816272155072977:ℚ)/60909321600000000000000000000000000000),((-19752568685555346550671481:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3182237423:ℚ)/5000000000),((332771029:ℚ)/500000000),((32160136807:ℚ)/55300000000),((4170461:ℚ)/6000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2891154033:ℚ)/5000000000),((-8988418064169440896341759004387435081540720352013567869:ℚ)/634171413750000000000000000000000000000000000000000000000),((-4971474452559458633538929:ℚ)/23104000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((6602337011:ℚ)/10000000000),((1354866517:ℚ)/2000000000),((66461033099:ℚ)/112500000000),((1508466517:ℚ)/2212000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5181668963:ℚ)/10000000000),((-9496535227773981867126961946345465429518425512754022097:ℚ)/593261718750000000000000000000000000000000000000000000000),((-19952890359485663668656121:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6721258899:ℚ)/10000000000),((6893239197:ℚ)/10000000000),((67531330091:ℚ)/114400000000),((2553746399:ℚ)/3750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2428202397:ℚ)/5000000000),((-2741579009311247369377121447666925850995456633252384329:ℚ)/170135680000000000000000000000000000000000000000000000000),((-19986468945825860951094201:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1368035013:ℚ)/2000000000),((7012140683:ℚ)/10000000000),((13720315117:ℚ)/23260000000),((7780140683:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1127434909:ℚ)/2500000000),((-191234774550038728376973026717542543427389931929761239:ℚ)/11797783102500000000000000000000000000000000000000000000),((-800804100414938946248169:ℚ)/3696640000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((9:ℚ)/16),((5:ℚ)/8),((6959085791:ℚ)/10000000000),((3535794791:ℚ)/5000000000),((69671772119:ℚ)/117250000000),((3919794791:ℚ)/5815000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((4136266383:ℚ)/10000000000),((-3676855148415241961764453244174633072542075566494608459:ℚ)/215879692382812500000000000000000000000000000000000000000),((-20053791124919718309457681:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7018539197:ℚ)/10000000000),((713103729:ℚ)/1000000000),((70206852773:ℚ)/118200000000),((789903729:ℚ)/1172500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((787421039:ℚ)/2000000000),((-326128607214849887375478229048322931144004600250208199:ℚ)/19113432500000000000000000000000000000000000000000000000),((-20070656097069561175022809:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((353899567:ℚ)/500000000),((7190483837:ℚ)/10000000000),((3537096103:ℚ)/5957500000),((7958483837:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((931976107:ℚ)/2500000000),((-13551850998553831449039894595676741673715706141759621:ℚ)/792909134003906250000000000000000000000000000000000000),((-139110352191111619849:ℚ)/640000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((28549769:ℚ)/40000000),((7249929249:ℚ)/10000000000),((285107921:ℚ)/480400000),((8017929249:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((219178979:ℚ)/625000000),((-148265633942011470695507706092155489249921684321:ℚ)/8661618005000000000000000000000000000000000000000),((-321670838568430995361:ℚ)/1478656000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((3598445979:ℚ)/5000000000),((1461874711:ℚ)/2000000000),((35906013811:ℚ)/60525000000),((1615474711:ℚ)/2402000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((6543159:ℚ)/20000000),((-527864700601775720706098373683775959477152186778191139:ℚ)/30794410722656250000000000000000000000000000000000000000),((-5030333441850059208150441:ℚ)/23104000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((725634049:ℚ)/1000000000),((368440839:ℚ)/500000000),((7234706441:ℚ)/12200000000),((135613613:ℚ)/201750000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3018718599:ℚ)/10000000000),((-38957767334789092979682889783244019617191347722769241:ℚ)/2269810000000000000000000000000000000000000000000000000),((-201382539335616654936401:ℚ)/924160000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((58526303:ℚ)/80000000),((1497540017:ℚ)/2000000000),((583056727:ℚ)/991200000),((1651140017:ℚ)/2440000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((137170999:ℚ)/500000000),((-557509149808394989634129862894702004307142010967:ℚ)/33813598560000000000000000000000000000000000000000),((-1289932026651914145809:ℚ)/5914624000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((743467931:ℚ)/1000000000),((7606579357:ℚ)/10000000000),((7395211379:ℚ)/12580000000),((141942023:ℚ)/210000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((522398873:ℚ)/2500000000),((-40182091621470787794663767479096436463936063467971:ℚ)/2430255751953125000000000000000000000000000000000000),((-201890973593076308942761:ℚ)/924160000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((29506119:ℚ)/39062500),((7844326511:ℚ)/10000000000),((293055071:ℚ)/506250000),((8612326511:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((552987673:ℚ)/5000000000),((-91762578454310700149993837195518097297547767117:ℚ)/6006774902343750000000000000000000000000000000000),((-154289719750124858643:ℚ)/705078125000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7791328689:ℚ)/10000000000),((609117539:ℚ)/625000000),((77161958201:ℚ)/160000000000),((657117539:ℚ)/810000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-217148656603289099275658151533446657:ℚ)/96000000000000000000000000000000000000),((-1751761:ℚ)/8000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((2423244383:ℚ)/2500000000),((6773852053:ℚ)/5000000000),((23569199447:ℚ)/55200000000),((7157852053:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((12247173088858134838782599:ℚ)/1523520000000000000000000000),((-1751761:ℚ)/8000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC26
#check @N11Formalization.C450Source13GroupedC26.bound
#print axioms N11Formalization.C450Source13GroupedC26.valid0
#print axioms N11Formalization.C450Source13GroupedC26.valid1
#print axioms N11Formalization.C450Source13GroupedC26.valid2
#print axioms N11Formalization.C450Source13GroupedC26.valid3
#print axioms N11Formalization.C450Source13GroupedC26.valid4
#print axioms N11Formalization.C450Source13GroupedC26.valid5
#print axioms N11Formalization.C450Source13GroupedC26.valid6
#print axioms N11Formalization.C450Source13GroupedC26.valid7
#print axioms N11Formalization.C450Source13GroupedC26.valid8
#print axioms N11Formalization.C450Source13GroupedC26.valid9
#print axioms N11Formalization.C450Source13GroupedC26.valid10
#print axioms N11Formalization.C450Source13GroupedC26.valid11
#print axioms N11Formalization.C450Source13GroupedC26.valid12
#print axioms N11Formalization.C450Source13GroupedC26.valid13
#print axioms N11Formalization.C450Source13GroupedC26.valid14
#print axioms N11Formalization.C450Source13GroupedC26.valid15
#print axioms N11Formalization.C450Source13GroupedC26.bound
#print axioms N11Formalization.C450Source13GroupedC26.endpoint_checks
