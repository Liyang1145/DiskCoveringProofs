import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((58511029:ℚ)/100000000),((319508371:ℚ)/500000000),((229933087:ℚ)/534000000),((2812558597:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6921401569:ℚ)/10000000000),((240320128644371410619:ℚ)/9505200000000000000000),((-5571215962234821071657483:ℚ)/18483200000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3164263461:ℚ)/5000000000),((265147871:ℚ)/400000000),((12212790383:ℚ)/27650000000),((2316835097:ℚ)/4272000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((366767909:ℚ)/625000000),((45488385333155263360127942638142317:ℚ)/2293567500000000000000000000000000000),((-3654410820166959247454483:ℚ)/11829248000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((410444571:ℚ)/625000000),((686715733:ℚ)/1000000000),((1571333713:ℚ)/3575000000),((5959010131:ℚ)/11060000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1318622717:ℚ)/2500000000),((18826325650539614425837236311481:ℚ)/983125000000000000000000000000000),((-23081321568106463926314107:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((3402813363:ℚ)/5000000000),((1746590983:ℚ)/2500000000),((12928440089:ℚ)/29075000000),((1373285171:ℚ)/2600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((576617719:ℚ)/1250000000),((21581094783745854315298581212493227:ℚ)/1268033437500000000000000000000000000),((-145978247055342812698491107:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6924858529:ℚ)/10000000000),((7105555773:ℚ)/10000000000),((26214575587:ℚ)/59100000000),((61258890411:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4246922153:ℚ)/10000000000),((9796256581016401958399620875344771:ℚ)/582135000000000000000000000000000000),((-7042660300450785772029839681:ℚ)/22179840000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((7044074753:ℚ)/10000000000),((3612366779:ℚ)/5000000000),((26572224259:ℚ)/60050000000),((31046567453:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3848574983:ℚ)/10000000000),((180279685978925133626552549462813713:ℚ)/10818007500000000000000000000000000000),((-589847898818894540357533083:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((358163807:ℚ)/500000000),((7343897949:ℚ)/10000000000),((1346491421:ℚ)/3050000000),((62927285643:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((27252327:ℚ)/80000000),((153750025907987521869296559186771:ℚ)/9302500000000000000000000000000000),((-7113499607240274374387509889:ℚ)/22179840000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((728246339:ℚ)/1000000000),((118471703:ℚ)/156250000),((2728739017:ℚ)/6290000000),((1009301921:ℚ)/1906250000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((72521861:ℚ)/250000000),((353578386608947968128103341208351:ℚ)/19782050000000000000000000000000000),((-290403341694552384624721:ℚ)/902500000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((3760399029:ℚ)/5000000000),((7820433427:ℚ)/10000000000),((14001197087:ℚ)/32400000000),((66263033989:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((180619241:ℚ)/1250000000),((6181298865911369352118277507462929:ℚ)/349920000000000000000000000000000000),((-79259240434205383:ℚ)/243200000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((7759083537:ℚ)/10000000000),((389004459:ℚ)/400000000),((28717250611:ℚ)/80000000000),((1061277071:ℚ)/1728000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((155427330474686975655933552606322369:ℚ)/4800000000000000000000000000000000000),((-167576913:ℚ)/512000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((4832009619:ℚ)/5000000000),((13530594839:ℚ)/10000000000),((17216028857:ℚ)/55200000000),((106234163873:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5075823956933566631383499:ℚ)/101568000000000000000000000),((-167576913:ℚ)/512000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC23
#check @N11Formalization.C450Source19GroupedC23.bound
#print axioms N11Formalization.C450Source19GroupedC23.valid0
#print axioms N11Formalization.C450Source19GroupedC23.valid1
#print axioms N11Formalization.C450Source19GroupedC23.valid2
#print axioms N11Formalization.C450Source19GroupedC23.valid3
#print axioms N11Formalization.C450Source19GroupedC23.valid4
#print axioms N11Formalization.C450Source19GroupedC23.valid5
#print axioms N11Formalization.C450Source19GroupedC23.valid6
#print axioms N11Formalization.C450Source19GroupedC23.valid7
#print axioms N11Formalization.C450Source19GroupedC23.valid8
#print axioms N11Formalization.C450Source19GroupedC23.valid9
#print axioms N11Formalization.C450Source19GroupedC23.valid10
#print axioms N11Formalization.C450Source19GroupedC23.bound
#print axioms N11Formalization.C450Source19GroupedC23.endpoint_checks
