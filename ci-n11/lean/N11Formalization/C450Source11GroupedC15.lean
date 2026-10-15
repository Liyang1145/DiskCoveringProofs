import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((776510057:ℚ)/1250000000),((1342638361:ℚ)/2000000000),((-766638361:ℚ)/9920000000),((23489943:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1227899291:ℚ)/2000000000),((14574717588155495037380826849632739:ℚ)/476656000000000000000000000000000000),((-616057496433968348167911:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6687823039:ℚ)/10000000000),((85401857:ℚ)/125000000),((-49401857:ℚ)/667500000),((-287823039:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4949831467:ℚ)/10000000000),((63513796416506263426877681772709339403125894356533518098973:ℚ)/2143284933131250000000000000000000000000000000000000000000000),((-2992223957981344587659:ℚ)/144400000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((272269697:ℚ)/400000000),((3475549097:ℚ)/5000000000),((-2035549097:ℚ)/27175000000),((-16269697:ℚ)/4424000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((115241063:ℚ)/250000000),((813801501373528840468836073014233192002137337189392157:ℚ)/27573773069850000000000000000000000000000000000000000000),((-5016299159476268973720519:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((6925655979:ℚ)/10000000000),((3505285227:ℚ)/5000000000),((-2065285227:ℚ)/27650000000),((-525655979:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2122187449:ℚ)/5000000000),((8800383967877739974525487770043424182184381167180927016003:ℚ)/299842983018701171875000000000000000000000000000000000000000),((-15745933703349096974124317:ℚ)/693120000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((3492555331:ℚ)/5000000000),((1767510267:ℚ)/2500000000),((-1047510267:ℚ)/13943750000),((-292555331:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((810045119:ℚ)/2000000000),((852074767543599351187333573425453401346040260997471810903:ℚ)/29082280397415161132812500000000000000000000000000000000000),((-4022194698178797843804797:ℚ)/173280000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((7044563997:ℚ)/10000000000),((7129510077:ℚ)/10000000000),((-1416503359:ℚ)/18750000000),((-644563997:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3846859927:ℚ)/10000000000),((2002065626482323760315465992521652288037469006124821071:ℚ)/68447057279296875000000000000000000000000000000000000000),((-65726085313526243935465517:ℚ)/2772480000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((7104016017:ℚ)/10000000000),((89862219:ℚ)/125000000),((-53862219:ℚ)/709062500),((-704016017:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1816363167:ℚ)/5000000000),((620043791007957307494644790872342788423489431482947068626397:ℚ)/21232082185600000000000000000000000000000000000000000000000000),((-10483850941896206445953:ℚ)/433200000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((1790866689:ℚ)/2500000000),((3624221719:ℚ)/5000000000),((-2184221719:ℚ)/28600000000),((-190866689:ℚ)/28837500000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3405790099:ℚ)/10000000000),((6658013951834596662599971938822990848176117363705199:ℚ)/228337626112461090087890625000000000000000000000000000),((-5705566510225228130862151:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((1444583249:ℚ)/2000000000),((7307907867:ℚ)/10000000000),((-1475969289:ℚ)/19225000000),((-164583249:ℚ)/23260000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((395411559:ℚ)/1250000000),((1761045568299964935859862751039191617688842931623764548449:ℚ)/60483301372150000000000000000000000000000000000000000000000),((-69836542336649256619447997:ℚ)/2772480000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/8),((-1:ℚ)/16),((1456472903:ℚ)/2000000000),((7367370843:ℚ)/10000000000),((-4487370843:ℚ)/58150000000),((-176472903:ℚ)/23450000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2901329239:ℚ)/10000000000),((2725341808161671171676857615455276607438894116641743425629:ℚ)/93732084036718750000000000000000000000000000000000000000000),((-71205879408478114220886077:ℚ)/2772480000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1468362319:ℚ)/2000000000),((3713416201:ℚ)/5000000000),((-324773743:ℚ)/4187500000),((-188362319:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1307024707:ℚ)/5000000000),((13386754552877728058457590074144660441183703452482969431:ℚ)/461015991900000000000000000000000000000000000000000000000),((-6047900835677542856317191:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((1480251503:ℚ)/2000000000),((7545751403:ℚ)/10000000000),((-4665751403:ℚ)/59100000000),((-200251503:ℚ)/24020000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((45838937:ℚ)/200000000),((371792363741153193121107858902309769723648340243323639377:ℚ)/12797540602387500000000000000000000000000000000000000000000),((-24631801252848286209543519:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((3760072991:ℚ)/5000000000),((766466513:ℚ)/1000000000),((-478466513:ℚ)/6005000000),((-560072991:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1450900361:ℚ)/10000000000),((49382212794439965005124666337977207207846815427319517797911:ℚ)/1703776131250000000000000000000000000000000000000000000000000),((-1681653890485863:ℚ)/60800000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7639030129:ℚ)/10000000000),((8140271939:ℚ)/10000000000),((-5260271939:ℚ)/61000000000),((-413010043:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((299362824605613841135631296053416882448462598921719047029:ℚ)/10245657600000000000000000000000000000000000000000000000000),((-1814073:ℚ)/64000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((2028631831:ℚ)/2500000000),((10042121899:ℚ)/10000000000),((-7162121899:ℚ)/64800000000),((-428631831:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((976068406954484385919414568454588475859596895352924517831:ℚ)/32400000000000000000000000000000000000000000000000000000000),((-1814073:ℚ)/64000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((5008021613:ℚ)/5000000000),((138442923:ℚ)/100000000),((-109642923:ℚ)/800000000),((-602673871:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((7726295000008245034330412778757625771631652595342991253:ℚ)/233606400000000000000000000000000000000000000000000000000),((-1814073:ℚ)/64000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC15
#check @N11Formalization.C450Source11GroupedC15.bound
#print axioms N11Formalization.C450Source11GroupedC15.valid0
#print axioms N11Formalization.C450Source11GroupedC15.valid1
#print axioms N11Formalization.C450Source11GroupedC15.valid2
#print axioms N11Formalization.C450Source11GroupedC15.valid3
#print axioms N11Formalization.C450Source11GroupedC15.valid4
#print axioms N11Formalization.C450Source11GroupedC15.valid5
#print axioms N11Formalization.C450Source11GroupedC15.valid6
#print axioms N11Formalization.C450Source11GroupedC15.valid7
#print axioms N11Formalization.C450Source11GroupedC15.valid8
#print axioms N11Formalization.C450Source11GroupedC15.valid9
#print axioms N11Formalization.C450Source11GroupedC15.valid10
#print axioms N11Formalization.C450Source11GroupedC15.valid11
#print axioms N11Formalization.C450Source11GroupedC15.valid12
#print axioms N11Formalization.C450Source11GroupedC15.valid13
#print axioms N11Formalization.C450Source11GroupedC15.valid14
#print axioms N11Formalization.C450Source11GroupedC15.valid15
#print axioms N11Formalization.C450Source11GroupedC15.bound
#print axioms N11Formalization.C450Source11GroupedC15.endpoint_checks
