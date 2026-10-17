import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((11:ℚ)/16),((3:ℚ)/4),((2674354639:ℚ)/5000000000),((283902277:ℚ)/500000000),((37737901029:ℚ)/51500000000),((1067706831:ℚ)/1240000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7900954117:ℚ)/10000000000),((-51665649534301037036439858693558827343:ℚ)/170738593750000000000000000000000000000),((-15590057361982120554179139:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((223509691:ℚ)/400000000),((5917137667:ℚ)/10000000000),((3124206601:ℚ)/4272000000),((22071413001:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1861978739:ℚ)/2500000000),((-575027513368621723523084909866284333327719153930059:ℚ)/1903416300000000000000000000000000000000000000000000),((-6153253769674903645215783699:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((5826665199:ℚ)/10000000000),((1207328317:ℚ)/2000000000),((80733317189:ℚ)/108700000000),((1495328317:ℚ)/1780000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6971634347:ℚ)/10000000000),((-7559415776612964651912918177945466205941805513432503470437:ℚ)/24081853181250000000000000000000000000000000000000000000000),((-244438817803815835527217299:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((2973044517:ℚ)/5000000000),((3078059681:ℚ)/5000000000),((41023489687:ℚ)/55300000000),((11394179043:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3361589839:ℚ)/5000000000),((-62099572604773421163253130890340040054395478878949721831:ℚ)/198178566796875000000000000000000000000000000000000000000),((-1517021957001767447573939451:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((3032744763:ℚ)/5000000000),((6275572337:ℚ)/10000000000),((41680192393:ℚ)/56250000000),((23146717011:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6466765137:ℚ)/10000000000),((-115985941859894927171911139862561725805923603938912189601:ℚ)/370788574218750000000000000000000000000000000000000000000),((-6024605826984399589255599579:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6184867871:ℚ)/10000000000),((3167644959:ℚ)/5000000000),((84673546581:ℚ)/113450000000),((1295881653:ℚ)/1562500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1550344407:ℚ)/2500000000),((-2904459663756703655560816293578406989232106987952341893519:ℚ)/9126274303906250000000000000000000000000000000000000000000),((-1500660007593786035073346171:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6244549089:ℚ)/10000000000),((6395001761:ℚ)/10000000000),((85330039979:ℚ)/114400000000),((23505005283:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6064944451:ℚ)/10000000000),((-64011645651468641242582186712632569492830108665616059:ℚ)/201344000000000000000000000000000000000000000000000000),((-5980524355953812624200553211:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((197007037:ℚ)/312500000),((806838501:ℚ)/1250000000),((895692469:ℚ)/1201562500),((269137773:ℚ)/325000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((11851571:ℚ)/20000000),((-2582580959523573320227425823512355479382238078588137:ℚ)/8131681841611862182617187500000000000000000000000000),((-93097793662485774742444291:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6363896281:ℚ)/10000000000),((8143011:ℚ)/12500000),((86642859091:ℚ)/116300000000),((9943011:ℚ)/12015625),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((5783700799:ℚ)/10000000000),((-124770119137894753191399654602661219129303665131339886881:ℚ)/393259436750000000000000000000000000000000000000000000000),((-9274755211432437648211:ℚ)/23104000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((3211781253:ℚ)/5000000000),((657410427:ℚ)/1000000000),((43649593783:ℚ)/58625000000),((2404231281:ℚ)/2907500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2819232947:ℚ)/5000000000),((-42764710259304626673363328406814689051818937204079138697:ℚ)/134924807739257812500000000000000000000000000000000000000),((-59132779699077288383820739:ℚ)/147865600000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6483223977:ℚ)/10000000000),((6633794547:ℚ)/10000000000),((87955463747:ℚ)/118200000000),((3460197663:ℚ)/4187500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((686228433:ℚ)/1250000000),((-272340015007648088328424277830242627589360416796804761299:ℚ)/860104462500000000000000000000000000000000000000000000000),((-5890562689542818264108728819:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((654288081:ℚ)/1000000000),((6693479757:ℚ)/10000000000),((8861168891:ℚ)/11915000000),((8133479757:ℚ)/9850000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5337497813:ℚ)/10000000000),((-10032617827699081960765795941358931248310018355512989523:ℚ)/31716365360156250000000000000000000000000000000000000000),((-5867697485429579976843366259:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3301266559:ℚ)/5000000000),((6753160021:ℚ)/10000000000),((44633932149:ℚ)/60050000000),((24579480063:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5181147959:ℚ)/10000000000),((-26730337052835831297251790026727721860865879165984645359:ℚ)/84586113330078125000000000000000000000000000000000000000),((-5844682349424560387162615331:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((6662181009:ℚ)/10000000000),((343625309:ℚ)/500000000),((89923991099:ℚ)/122000000000),((1246875927:ℚ)/1501250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((125509971:ℚ)/250000000),((-3520771853507151139148143205715950896043523990095258045249:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-14495505622183708738981971:ℚ)/36966400000000000000000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((3390731977:ℚ)/5000000000),((888893011:ℚ)/1250000000),((45618051747:ℚ)/62900000000),((3206679033:ℚ)/3812500000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4683864353:ℚ)/10000000000),((-116403323463402948753929659169799637534553398460140021233:ℚ)/388840920312500000000000000000000000000000000000000000000),((-89116289435228155975148211:ℚ)/231040000000000000000000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((7019981239:ℚ)/10000000000),((1469942963:ℚ)/2000000000),((93859793629:ℚ)/129600000000),((5273828889:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((786431223:ℚ)/2000000000),((-150544329238420510429298220720239521946574138055430237573:ℚ)/503884800000000000000000000000000000000000000000000000000),((-224251322637146570015339379:ℚ)/591462400000000000000000000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((1814609627:ℚ)/2500000000),((925644047:ℚ)/1000000000),((24120705897:ℚ)/40000000000),((1069644047:ℚ)/1080000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3009419559:ℚ)/10000000000),((-4899617799508373851311506762723965718812293106243136067:ℚ)/25000000000000000000000000000000000000000000000000000000),((-381007281:ℚ)/1024000000)⟩
theorem valid16 : Valid source28 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9164452363:ℚ)/10000000000),((2612863749:ℚ)/2000000000),((117448975993:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-352864433935270814310162946481216780849:ℚ)/2691145728000000000000000000000000000000),((-381007281:ℚ)/1024000000)⟩
theorem valid17 : Valid source28 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC28
#check @N11Formalization.C450Source28GroupedC28.bound
#print axioms N11Formalization.C450Source28GroupedC28.valid0
#print axioms N11Formalization.C450Source28GroupedC28.valid1
#print axioms N11Formalization.C450Source28GroupedC28.valid2
#print axioms N11Formalization.C450Source28GroupedC28.valid3
#print axioms N11Formalization.C450Source28GroupedC28.valid4
#print axioms N11Formalization.C450Source28GroupedC28.valid5
#print axioms N11Formalization.C450Source28GroupedC28.valid6
#print axioms N11Formalization.C450Source28GroupedC28.valid7
#print axioms N11Formalization.C450Source28GroupedC28.valid8
#print axioms N11Formalization.C450Source28GroupedC28.valid9
#print axioms N11Formalization.C450Source28GroupedC28.valid10
#print axioms N11Formalization.C450Source28GroupedC28.valid11
#print axioms N11Formalization.C450Source28GroupedC28.valid12
#print axioms N11Formalization.C450Source28GroupedC28.valid13
#print axioms N11Formalization.C450Source28GroupedC28.valid14
#print axioms N11Formalization.C450Source28GroupedC28.valid15
#print axioms N11Formalization.C450Source28GroupedC28.valid16
#print axioms N11Formalization.C450Source28GroupedC28.valid17
#print axioms N11Formalization.C450Source28GroupedC28.bound
#print axioms N11Formalization.C450Source28GroupedC28.endpoint_checks
