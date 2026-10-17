import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((9:ℚ)/16),((5:ℚ)/8),((5318954157:ℚ)/10000000000),((2828918663:ℚ)/5000000000),((67710587413:ℚ)/103000000000),((3852918663:ℚ)/4960000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7955915061:ℚ)/10000000000),((-2697936423268999201780257082068043678058136108319995473:ℚ)/7855290880000000000000000000000000000000000000000000000),((-1678721890881449008571015991:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((868669:ℚ)/1562500),((2949148243:ℚ)/5000000000),((10918021:ℚ)/16687500),((3973148243:ℚ)/5150000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7502612927:ℚ)/10000000000),((-1952777466027073448941323818589815591966917054848581017:ℚ)/5698400566406250000000000000000000000000000000000000000),((-1657586376485296562900251711:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((5799789767:ℚ)/10000000000),((1504611773:ℚ)/2500000000),((72038107903:ℚ)/108700000000),((2016611773:ℚ)/2670000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7026532411:ℚ)/10000000000),((-1514368563872227355544123848821648598792230173701933249:ℚ)/4310444829375000000000000000000000000000000000000000000),((-412663223532898205285430431:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((2959934487:ℚ)/5000000000),((383659297:ℚ)/625000000),((36559410383:ℚ)/55300000000),((511659297:ℚ)/679375000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1355676711:ℚ)/2000000000),((-84833111909019537564277693133578574369151027034639:ℚ)/241911112635135650634765625000000000000000000000000),((-25614580941358821071502951:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((6039901769:ℚ)/10000000000),((6258603999:ℚ)/10000000000),((74199115921:ℚ)/112500000000),((8306603999:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((815304671:ℚ)/1250000000),((-1486578735867984100795443654460814318836828097711729:ℚ)/4246683574218750000000000000000000000000000000000000),((-6510854741213622185345091239:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((3079945277:ℚ)/5000000000),((6378615197:ℚ)/10000000000),((37639507493:ℚ)/57200000000),((8426615197:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3128853751:ℚ)/5000000000),((-44470236791120621952999059882976620324902327550995036427:ℚ)/127254638671875000000000000000000000000000000000000000000),((-6463178102072112038750992351:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((3139918783:ℚ)/5000000000),((129971691:ℚ)/200000000),((38179269047:ℚ)/58150000000),((170931691:ℚ)/228800000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2991499091:ℚ)/5000000000),((-276133358104286071173862619286028127873776387982771:ℚ)/791471183360000000000000000000000000000000000000000),((-2565721294983817584318959:ℚ)/5914624000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6399744893:ℚ)/10000000000),((1323702823:ℚ)/2000000000),((77437704037:ℚ)/118200000000),((1733302823:ℚ)/2326000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((142420889:ℚ)/250000000),((-404798647351709147062871215410413127275715192652248001:ℚ)/1162081635596250000000000000000000000000000000000000000),((-254569222135892035646656631:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1303922897:ℚ)/2000000000),((6738405819:ℚ)/10000000000),((15703306073:ℚ)/24020000000),((8786405819:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1079473449:ℚ)/2000000000),((-323361908259609203143179162607920366826262649674544272921:ℚ)/929686913516250000000000000000000000000000000000000000000),((-6312960427373077061469604879:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((6639448167:ℚ)/10000000000),((6858261463:ℚ)/10000000000),((79595033503:ℚ)/122000000000),((8906261463:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5082209849:ℚ)/10000000000),((-22938871626162967323433272361856993159257525559478871171:ℚ)/66044837288125000000000000000000000000000000000000000000),((-6260493214435871379274495191:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1351849529:ℚ)/2000000000),((283914849:ℚ)/400000000),((16134645761:ℚ)/25160000000),((365834849:ℚ)/488000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1187051849:ℚ)/2500000000),((-11626024940652004456069113949622527941167626124077831:ℚ)/34265051760000000000000000000000000000000000000000000),((-9817087544614462687782439:ℚ)/23658496000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((3499375149:ℚ)/5000000000),((7337355711:ℚ)/10000000000),((41414376341:ℚ)/64800000000),((9385355711:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((500554373:ℚ)/1250000000),((-922863253436426006729379381265721597813002526238049499:ℚ)/2723988285000000000000000000000000000000000000000000000),((-6022378972893854898851772519:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7238134109:ℚ)/10000000000),((1849961297:ℚ)/2000000000),((84983206981:ℚ)/160000000000),((753187099:ℚ)/864000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((619655731:ℚ)/2000000000),((-18471250362203476187052754860770179440809540934601:ℚ)/75582720000000000000000000000000000000000000000000),((-19372993454659619:ℚ)/48640000000000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((9149954771:ℚ)/10000000000),((6532182101:ℚ)/5000000000),((102189592939:ℚ)/220800000000),((7556182101:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-149543833107046232280722044437350891:ℚ)/883200000000000000000000000000000000),((-411260821:ℚ)/1024000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC26
#check @N11Formalization.C450Source33GroupedC26.bound
#print axioms N11Formalization.C450Source33GroupedC26.valid0
#print axioms N11Formalization.C450Source33GroupedC26.valid1
#print axioms N11Formalization.C450Source33GroupedC26.valid2
#print axioms N11Formalization.C450Source33GroupedC26.valid3
#print axioms N11Formalization.C450Source33GroupedC26.valid4
#print axioms N11Formalization.C450Source33GroupedC26.valid5
#print axioms N11Formalization.C450Source33GroupedC26.valid6
#print axioms N11Formalization.C450Source33GroupedC26.valid7
#print axioms N11Formalization.C450Source33GroupedC26.valid8
#print axioms N11Formalization.C450Source33GroupedC26.valid9
#print axioms N11Formalization.C450Source33GroupedC26.valid10
#print axioms N11Formalization.C450Source33GroupedC26.valid11
#print axioms N11Formalization.C450Source33GroupedC26.valid12
#print axioms N11Formalization.C450Source33GroupedC26.valid13
#print axioms N11Formalization.C450Source33GroupedC26.bound
#print axioms N11Formalization.C450Source33GroupedC26.endpoint_checks
