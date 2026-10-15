import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((5947870753:ℚ)/10000000000),((812161921:ℚ)/1250000000),((13307870753:ℚ)/53400000000),((4356485763:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3359707279:ℚ)/5000000000),((3583999978627725456485521921813473066581:ℚ)/33980329584000000000000000000000000000000),((-15900757441358887522556507:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6428057579:ℚ)/10000000000),((3368484577:ℚ)/5000000000),((13788057579:ℚ)/55300000000),((5928484577:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5627389363:ℚ)/10000000000),((149404121823809285512711368300424575312861327299606965991611:ℚ)/1539899035150000000000000000000000000000000000000000000000000),((-269726661199752881643081083:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((833484961:ℚ)/1250000000),((3428375127:ℚ)/5000000000),((584494987:ℚ)/2343750000),((2566446483:ℚ)/7900000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5004794709:ℚ)/10000000000),((2596039063155522426571835596929318435330619018926207007:ℚ)/27733443750000000000000000000000000000000000000000000000),((-277350799050141579304805483:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((6787731089:ℚ)/10000000000),((6976496671:ℚ)/10000000000),((14147731089:ℚ)/57200000000),((4032165557:ℚ)/12500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4665565033:ℚ)/10000000000),((23284605463975277129830437475058305808756841146198395162913:ℚ)/249621582031250000000000000000000000000000000000000000000000),((-1122773000727943595505200507:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1726886353:ℚ)/2500000000),((3548105067:ℚ)/5000000000),((3566886353:ℚ)/14537500000),((18324315201:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4301875391:ℚ)/10000000000),((36789454422090702648311924743426134829176377501940240419026389:ℚ)/395519173778300000000000000000000000000000000000000000000000000),((-284018726105905395913431203:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1405464901:ℚ)/2000000000),((7215892257:ℚ)/10000000000),((959154967:ℚ)/3940000000),((37007676771:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((61044717:ℚ)/156250000),((8853041326638305314202000015937085966004816662001654764179111:ℚ)/95387534255192187500000000000000000000000000000000000000000000),((-60489956367202698562641017:ℚ)/155648000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7147070097:ℚ)/10000000000),((7455168429:ℚ)/10000000000),((14507070097:ℚ)/61000000000),((12575168429:ℚ)/39400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((693960111:ℚ)/2000000000),((134892767035976815625021931932975795771209191701981326794049:ℚ)/1422421646650000000000000000000000000000000000000000000000000),((-1158548199005027157663837107:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((7386467139:ℚ)/10000000000),((1983351281:ℚ)/2500000000),((14746467139:ℚ)/64800000000),((9790053843:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((594022223:ℚ)/2500000000),((28658353129837629604984910491378271688045945973271201284367:ℚ)/290863738476562500000000000000000000000000000000000000000000),((-390710012196961757:ℚ)/972800000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7864923863:ℚ)/10000000000),((9843254117:ℚ)/10000000000),((15224923863:ℚ)/80000000000),((14963254117:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3658464845310806707804264826201553627738274047873551777:ℚ)/31492800000000000000000000000000000000000000000000000000),((-421790317:ℚ)/1024000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9775440721:ℚ)/10000000000),((3413694853:ℚ)/2500000000),((17135440721:ℚ)/110400000000),((14081084559:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((11560722156547836264136407070031262876833:ℚ)/76176000000000000000000000000000000000000),((-421790317:ℚ)/1024000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC19
#check @N11Formalization.C450Source25GroupedC19.bound
#print axioms N11Formalization.C450Source25GroupedC19.valid0
#print axioms N11Formalization.C450Source25GroupedC19.valid1
#print axioms N11Formalization.C450Source25GroupedC19.valid2
#print axioms N11Formalization.C450Source25GroupedC19.valid3
#print axioms N11Formalization.C450Source25GroupedC19.valid4
#print axioms N11Formalization.C450Source25GroupedC19.valid5
#print axioms N11Formalization.C450Source25GroupedC19.valid6
#print axioms N11Formalization.C450Source25GroupedC19.valid7
#print axioms N11Formalization.C450Source25GroupedC19.valid8
#print axioms N11Formalization.C450Source25GroupedC19.valid9
#print axioms N11Formalization.C450Source25GroupedC19.bound
#print axioms N11Formalization.C450Source25GroupedC19.endpoint_checks
