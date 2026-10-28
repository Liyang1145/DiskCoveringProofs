import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((119323463:ℚ)/200000000),((810964391:ℚ)/1250000000),((133723463:ℚ)/267000000),((8098679519:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3340317113:ℚ)/5000000000),((-12716243644499318543103279181:ℚ)/4758540750000000000000000000000),((-487909219065114883538657:ℚ)/2957312000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6441802079:ℚ)/10000000000),((3362732841:ℚ)/5000000000),((7161802079:ℚ)/13825000000),((33464595569:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5593399487:ℚ)/10000000000),((-263215424393680562081504568788403845772667262771447333:ℚ)/49544641699218750000000000000000000000000000000000000000),((-1233467294245966971841634673:ℚ)/7393280000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6679584073:ℚ)/10000000000),((3422167301:ℚ)/5000000000),((7399584073:ℚ)/14062500000),((33999505709:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((248630263:ℚ)/500000000),((-37668095155003003183150527150256704180403817507737859:ℚ)/5793571472167968750000000000000000000000000000000000000),((-1240377936461506047007361537:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((6798467913:ℚ)/10000000000),((3481599783:ℚ)/5000000000),((683497083:ℚ)/1300000000),((34534398047:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4634059197:ℚ)/10000000000),((-90692880008506415600473234201958898910862676058787:ℚ)/13731250000000000000000000000000000000000000000000000),((-1243849160258475888059168257:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((6917347301:ℚ)/10000000000),((11236209:ℚ)/16000000),((7637347301:ℚ)/14418750000),((10124171:ℚ)/16640000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2135422443:ℚ)/5000000000),((-100483064879430989061774817040695531813977567650514527:ℚ)/14051546222305297851562500000000000000000000000000000000),((-1247330993491359452705103753:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3488392697:ℚ)/5000000000),((221314399:ℚ)/312500000),((3848392697:ℚ)/7268750000),((2191829591:ℚ)/3604687500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4077936083:ℚ)/10000000000),((-690256161404041219065106962721842874853626661041617:ℚ)/96010604675292968750000000000000000000000000000000000),((-312268972570423101349530977:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/2),((9:ℚ)/16),((3518111227:ℚ)/5000000000),((223171563:ℚ)/312500000),((3878111227:ℚ)/7328125000),((2208544067:ℚ)/3634375000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3876002741:ℚ)/10000000000),((-1904100118401515200413482360812955803366345898090647:ℚ)/263525015115737915039062500000000000000000000000000000),((-312705860334671181959080137:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((7095658507:ℚ)/10000000000),((720091839:ℚ)/1000000000),((7815658507:ℚ)/14775000000),((7120826551:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3663548893:ℚ)/10000000000),((-12195121083889692147951572677942284090226747259327201:ℚ)/1679891528320312500000000000000000000000000000000000000),((-1252573647288571066449574697:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((3577546789:ℚ)/5000000000),((7260345913:ℚ)/10000000000),((3937546789:ℚ)/7446875000),((71743113217:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1719310441:ℚ)/5000000000),((-56458666327465113064324777192147177827531767233340983:ℚ)/7743253261756896972656250000000000000000000000000000000),((-313581627183192760640085513:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((7214527689:ℚ)/10000000000),((7319772603:ℚ)/10000000000),((7934527689:ℚ)/15012500000),((72277953427:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((399822969:ℚ)/1250000000),((-9676064640759436222364084428420891316951014916765881:ℚ)/1321658020782470703125000000000000000000000000000000000),((-1256082026188543662132986113:ℚ)/7393280000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((7273960863:ℚ)/10000000000),((7379198481:ℚ)/10000000000),((2664653621:ℚ)/5043750000),((72812786329:ℚ)/120100000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((587946787:ℚ)/2000000000),((-1964474741554988063245666493193544883558914042942543:ℚ)/267312593078613281250000000000000000000000000000000000),((-1257840200206729475994095857:ℚ)/7393280000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((7333393123:ℚ)/10000000000),((3719311783:ℚ)/5000000000),((8053393123:ℚ)/15250000000),((36673806047:ℚ)/60525000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1328286343:ℚ)/5000000000),((-163471906964486018925327205749216997527368395522165963:ℚ)/22166113281250000000000000000000000000000000000000000000),((-1259601031342326123195442937:ℚ)/7393280000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((739282449:ℚ)/1000000000),((1889367857:ℚ)/2500000000),((270427483:ℚ)/516250000),((18604310713:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1170143037:ℚ)/5000000000),((-1500507347968384722138795656786166558155810429403:ℚ)/214981069946289062500000000000000000000000000000000),((-12613645200950976194812753:ℚ)/73932800000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((7511684627:ℚ)/10000000000),((7676316331:ℚ)/10000000000),((8231684627:ℚ)/15725000000),((75486846979:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((305195277:ℚ)/2000000000),((-166837492130524541504486741122236110742371691010483:ℚ)/23732966327667236328125000000000000000000000000000000),((-1264899472410627266586950937:ℚ)/7393280000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7630541433:ℚ)/10000000000),((7913997779:ℚ)/10000000000),((927837937:ℚ)/1800000000),((77625980011:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-25474854572396955081623897199749619117325669153657:ℚ)/4050000000000000000000000000000000000000000000000000),((-87779291:ℚ)/512000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3934122819:ℚ)/5000000000),((9815138821:ℚ)/10000000000),((4294122819:ℚ)/10000000000),((94736249389:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((169051883703144080133283331311907:ℚ)/93750000000000000000000000000000000),((-87779291:ℚ)/512000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((9769529751:ℚ)/10000000000),((6808238907:ℚ)/5000000000),((3496509917:ℚ)/9200000000),((64474150163:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((93695989327529496496811:ℚ)/10580000000000000000000000),((-87779291:ℚ)/512000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC25
#check @N11Formalization.C450Source11GroupedC25.bound
#print axioms N11Formalization.C450Source11GroupedC25.valid0
#print axioms N11Formalization.C450Source11GroupedC25.valid1
#print axioms N11Formalization.C450Source11GroupedC25.valid2
#print axioms N11Formalization.C450Source11GroupedC25.valid3
#print axioms N11Formalization.C450Source11GroupedC25.valid4
#print axioms N11Formalization.C450Source11GroupedC25.valid5
#print axioms N11Formalization.C450Source11GroupedC25.valid6
#print axioms N11Formalization.C450Source11GroupedC25.valid7
#print axioms N11Formalization.C450Source11GroupedC25.valid8
#print axioms N11Formalization.C450Source11GroupedC25.valid9
#print axioms N11Formalization.C450Source11GroupedC25.valid10
#print axioms N11Formalization.C450Source11GroupedC25.valid11
#print axioms N11Formalization.C450Source11GroupedC25.valid12
#print axioms N11Formalization.C450Source11GroupedC25.valid13
#print axioms N11Formalization.C450Source11GroupedC25.valid14
#print axioms N11Formalization.C450Source11GroupedC25.valid15
#print axioms N11Formalization.C450Source11GroupedC25.valid16
#print axioms N11Formalization.C450Source11GroupedC25.bound
#print axioms N11Formalization.C450Source11GroupedC25.endpoint_checks
