import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/16),((1:ℚ)/2),((6986307:ℚ)/12500000),((1478552407:ℚ)/2500000000),((69704149:ℚ)/128750000),((2018552407:ℚ)/3100000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3722692289:ℚ)/5000000000),((-73705761716767041603248431893:ℚ)/533558105468750000000000000000),((-378926307027300723812439:ℚ)/902500000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((145729799:ℚ)/250000000),((1230832819:ℚ)/2000000000),((1436108593:ℚ)/2670000000),((1662832819:ℚ)/2575000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3483227237:ℚ)/5000000000),((-64074251485799470211295179854199944646314533570163:ℚ)/464701245117187500000000000000000000000000000000000),((-243068709129253133779071:ℚ)/577600000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1517286767:ℚ)/2500000000),((6274076021:ℚ)/10000000000),((14781007369:ℚ)/27175000000),((8434076021:ℚ)/13350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3229386879:ℚ)/5000000000),((-54326382005824600337065365595850801470940519247292114657:ℚ)/376278955957031250000000000000000000000000000000000000000),((-6128897031102588205477551:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6189059297:ℚ)/10000000000),((3196973729:ℚ)/5000000000),((59963415079:ℚ)/110600000000),((4276973729:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1547970351:ℚ)/2500000000),((-228264182475522179382119447651086117022389947229909854103:ℚ)/1585428534375000000000000000000000000000000000000000000000),((-1533464111475857661280551:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((6308931027:ℚ)/10000000000),((407111281:ℚ)/625000000),((60802517189:ℚ)/112500000000),((542111281:ℚ)/864062500),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1478672433:ℚ)/2500000000),((-425835180757033425661179785320694324222425196878465639717:ℚ)/2966308593750000000000000000000000000000000000000000000000),((-23976678129738621897771:ℚ)/56406250000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6428764347:ℚ)/10000000000),((6633577081:ℚ)/10000000000),((61641350429:ℚ)/114400000000),((8793577081:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5625646011:ℚ)/10000000000),((-11068210005265442215210208133125088402006976215559070031:ℚ)/77334400000000000000000000000000000000000000000000000000),((-6141417354219529333970871:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3274280603:ℚ)/5000000000),((844167379:ℚ)/1250000000),((31239964221:ℚ)/58150000000),((85705183:ℚ)/137500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2661394313:ℚ)/5000000000),((-43832886056713922568791910731689883259975034848686245791:ℚ)/307233934960937500000000000000000000000000000000000000000),((-96000320369220438326751:ℚ)/225625000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((333416171:ℚ)/500000000),((3436534023:ℚ)/5000000000),((1055304399:ℚ)/1970000000),((4516534023:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2501788907:ℚ)/5000000000),((-1698728033758442118984653137320175404344795466297261:ℚ)/11945895312500000000000000000000000000000000000000000),((-1536459948672919390568119:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6788052689:ℚ)/10000000000),((437047857:ℚ)/625000000),((64156368823:ℚ)/120100000000),((190682619:ℚ)/307812500),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1166156051:ℚ)/2500000000),((-4603190776707009384308702932745545811568272486176260801271:ℚ)/32481067518750000000000000000000000000000000000000000000000),((-24011234079859262046739:ℚ)/56406250000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((3453875301:ℚ)/5000000000),((7112433517:ℚ)/10000000000),((32497127107:ℚ)/61000000000),((9272433517:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4301227959:ℚ)/10000000000),((-200342053802165738848316264005093357955066235599389605193:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-6147129544881790587292479:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3513709323:ℚ)/5000000000),((3675842519:ℚ)/5000000000),((32915965261:ℚ)/62900000000),((4755842519:ℚ)/7625000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((3906536607:ℚ)/10000000000),((-52489667846706900573809717195441316230616290747613527551:ℚ)/388840920312500000000000000000000000000000000000000000000),((-1524749616967155926563671:ℚ)/3610000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7266670623:ℚ)/10000000000),((303633311:ℚ)/400000000),((67506694361:ℚ)/129600000000),((390033311:ℚ)/629000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((59453199:ℚ)/200000000),((-67598844308762238525811014635668380713769679835928985417:ℚ)/503884800000000000000000000000000000000000000000000000000),((-9750492698354372606631:ℚ)/23104000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((7505818787:ℚ)/10000000000),((4750587611:ℚ)/5000000000),((69180731509:ℚ)/160000000000),((5830587611:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((787970321:ℚ)/5000000000),((-451445563450786024263922413545741119:ℚ)/6000000000000000000000000000000000000),((-813525451902531:ℚ)/1900000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((9416163917:ℚ)/10000000000),((6656638019:ℚ)/5000000000),((82553147419:ℚ)/220800000000),((7736638019:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-12126283865795404077038701:ℚ)/507840000000000000000000000),((-86139:ℚ)/200000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC24
#check @N11Formalization.C450Source28GroupedC24.bound
#print axioms N11Formalization.C450Source28GroupedC24.valid0
#print axioms N11Formalization.C450Source28GroupedC24.valid1
#print axioms N11Formalization.C450Source28GroupedC24.valid2
#print axioms N11Formalization.C450Source28GroupedC24.valid3
#print axioms N11Formalization.C450Source28GroupedC24.valid4
#print axioms N11Formalization.C450Source28GroupedC24.valid5
#print axioms N11Formalization.C450Source28GroupedC24.valid6
#print axioms N11Formalization.C450Source28GroupedC24.valid7
#print axioms N11Formalization.C450Source28GroupedC24.valid8
#print axioms N11Formalization.C450Source28GroupedC24.valid9
#print axioms N11Formalization.C450Source28GroupedC24.valid10
#print axioms N11Formalization.C450Source28GroupedC24.valid11
#print axioms N11Formalization.C450Source28GroupedC24.valid12
#print axioms N11Formalization.C450Source28GroupedC24.valid13
#print axioms N11Formalization.C450Source28GroupedC24.bound
#print axioms N11Formalization.C450Source28GroupedC24.endpoint_checks
