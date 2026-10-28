import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((5662160463:ℚ)/10000000000),((776905143:ℚ)/1250000000),((2447386821:ℚ)/4450000000),((8752146287:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7302298339:ℚ)/10000000000),((-261423055277591032425411266080599:ℚ)/5507570312500000000000000000000000),((-4002532715770029641889061:ℚ)/10830000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6140227951:ℚ)/10000000000),((3227057473:ℚ)/5000000000),((7820227951:ℚ)/13825000000),((36083517257:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6301744321:ℚ)/10000000000),((-253356139443125907473206270143813671443745373319574767:ℚ)/4128720141601562500000000000000000000000000000000000000),((-1351427930856605446497247:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((1594775553:ℚ)/2500000000),((334644837:ℚ)/500000000),((2014775553:ℚ)/3575000000),((3715803533:ℚ)/5530000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5746997443:ℚ)/10000000000),((-400432901826472775246631931069070834439600748531611:ℚ)/6490161132812500000000000000000000000000000000000000),((-40611474414795667925851:ℚ)/108300000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3308942217:ℚ)/5000000000),((6812255983:ℚ)/10000000000),((4148942217:ℚ)/7268750000),((75390303847:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5140214663:ℚ)/10000000000),((-10131442547836794964561137894014991826831881559469961:ℚ)/150016569805145263671875000000000000000000000000000000),((-340485337627463261455497:ℚ)/902500000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6737243879:ℚ)/10000000000),((6931595493:ℚ)/10000000000),((8417243879:ℚ)/14775000000),((76464359437:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((96223013:ℚ)/200000000),((-84988763013010420536583220297287387691263791638311927:ℚ)/1259918646240234375000000000000000000000000000000000000),((-4088418113235320623144099:ℚ)/10830000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1371316717:ℚ)/2000000000),((881364527:ℚ)/1250000000),((1707316717:ℚ)/3002500000),((9692280743:ℚ)/14775000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4459946813:ℚ)/10000000000),((-2848468172048497181742405839311915824522497560825501:ℚ)/42293056665039062500000000000000000000000000000000000),((-1363559717311320557915577:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((3487952249:ℚ)/5000000000),((3585109519:ℚ)/5000000000),((4327952249:ℚ)/7625000000),((39305985671:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4080857733:ℚ)/10000000000),((-46563708799624693251205938671954452784038989925374913:ℚ)/692691040039062500000000000000000000000000000000000000),((-682101224772002425321749:ℚ)/1805000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((1419041501:ℚ)/2000000000),((1852193563:ℚ)/2500000000),((1755041501:ℚ)/3145000000),((20189742067:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((73304103:ℚ)/200000000),((-44234036415497052900944308003513426376290810784981:ℚ)/714781103515625000000000000000000000000000000000000),((-1357912566417540048832393:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((733376307:ℚ)/1000000000),((3823633599:ℚ)/5000000000),((100152923:ℚ)/180000000),((41452702391:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((265471799:ℚ)/1000000000),((-771439687743750523651653545074808199815845139:ℚ)/12500000000000000000000000000000000000000000000),((-965303424658851:ℚ)/2560000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3786128173:ℚ)/5000000000),((9553504903:ℚ)/10000000000),((4626128173:ℚ)/10000000000),((100061544127:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((854716793:ℚ)/10000000000),((-41140148123510262669906852910017:ℚ)/3906250000000000000000000000000000),((-92679366228265991:ℚ)/243200000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((75827969:ℚ)/80000000),((13360812751:ℚ)/10000000000),((89267969:ℚ)/220800000),((134327314759:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8319417393755224319:ℚ)/253920000000000000000),((-24419171:ℚ)/64000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC25
#check @N11Formalization.C450Source23GroupedC25.bound
#print axioms N11Formalization.C450Source23GroupedC25.valid0
#print axioms N11Formalization.C450Source23GroupedC25.valid1
#print axioms N11Formalization.C450Source23GroupedC25.valid2
#print axioms N11Formalization.C450Source23GroupedC25.valid3
#print axioms N11Formalization.C450Source23GroupedC25.valid4
#print axioms N11Formalization.C450Source23GroupedC25.valid5
#print axioms N11Formalization.C450Source23GroupedC25.valid6
#print axioms N11Formalization.C450Source23GroupedC25.valid7
#print axioms N11Formalization.C450Source23GroupedC25.valid8
#print axioms N11Formalization.C450Source23GroupedC25.valid9
#print axioms N11Formalization.C450Source23GroupedC25.valid10
#print axioms N11Formalization.C450Source23GroupedC25.bound
#print axioms N11Formalization.C450Source23GroupedC25.endpoint_checks
