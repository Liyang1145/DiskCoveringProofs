import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((2868587337:ℚ)/5000000000),((6286122741:ℚ)/10000000000),((26480111359:ℚ)/53400000000),((7966122741:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((447067377:ℚ)/625000000),((1490884415871995308091209:ℚ)/1425780000000000000000000000),((-7833199767748262668445089:ℚ)/21660000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6215241139:ℚ)/10000000000),((815620739:ℚ)/1250000000),((56306687973:ℚ)/110600000000),((1025620739:ℚ)/1668750000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6132273883:ℚ)/10000000000),((-40143594538398758757096691472041470039480266563905728691:ℚ)/4227809425000000000000000000000000000000000000000000000000),((-162710667832279437193:ℚ)/440673828125000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6454114941:ℚ)/10000000000),((3381859571:ℚ)/5000000000),((5270800417:ℚ)/10400000000),((4221859571:ℚ)/6912500000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5562792553:ℚ)/10000000000),((-35753025589858498367498239099485632949454826045165031:ℚ)/3515200000000000000000000000000000000000000000000000000),((-35311509034370130219497:ℚ)/95000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1338579347:ℚ)/2000000000),((3441532407:ℚ)/5000000000),((11930055429:ℚ)/23260000000),((4281532407:ℚ)/7150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2467879529:ℚ)/5000000000),((-142157070556292361025014209837150820348117486318513027:ℚ)/9831485918750000000000000000000000000000000000000000000),((-2032841374378943983634281:ℚ)/5415000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3406127989:ℚ)/5000000000),((1400478239:ℚ)/2000000000),((30242895923:ℚ)/59100000000),((1736478239:ℚ)/2907500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4593306111:ℚ)/10000000000),((-7044803321002556712800733530645301815777175481030953967:ℚ)/483808760156250000000000000000000000000000000000000000000),((-5724094847761053503857:ℚ)/15200000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((216612359:ℚ)/312500000),((7121699211:ℚ)/10000000000),((1916286513:ℚ)/3753125000),((2933899737:ℚ)/4925000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4225357243:ℚ)/10000000000),((-2416765902359965346266650364336050939359029286861511:ℚ)/165207252597808837890625000000000000000000000000000000),((-8181804000114469309436449:ℚ)/21660000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((7050916211:ℚ)/10000000000),((7240989727:ℚ)/10000000000),((62156413477:ℚ)/122000000000),((8920989727:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3824525757:ℚ)/10000000000),((-83209242686398165746913893698518807757751550099324846299:ℚ)/5674525000000000000000000000000000000000000000000000000000),((-2735424155083211189541667:ℚ)/7220000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7170219033:ℚ)/10000000000),((373976073:ℚ)/500000000),((62991533231:ℚ)/125800000000),((457976073:ℚ)/762500000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1689545797:ℚ)/5000000000),((-17409636988755450507292199495866795369784696358828681633:ℚ)/1555363681250000000000000000000000000000000000000000000000),((-20498480627982822146701:ℚ)/54150000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7408774247:ℚ)/10000000000),((3858996159:ℚ)/5000000000),((64661419729:ℚ)/129600000000),((4698996159:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((44959993:ℚ)/200000000),((-944871727795325890237329906724259941:ℚ)/83980800000000000000000000000000000000),((-5807966451854603:ℚ)/15200000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((7647267193:ℚ)/10000000000),((120301143:ℚ)/125000000),((66330870351:ℚ)/160000000000),((15700127:ℚ)/22500000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2301969995324183514741431685240723857:ℚ)/96000000000000000000000000000000000000),((-6177971:ℚ)/16000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((4776752449:ℚ)/5000000000),((13431237247:ℚ)/10000000000),((39837267143:ℚ)/110400000000),((15111237247:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((357662541000158890634423161:ℚ)/6094080000000000000000000000),((-6177971:ℚ)/16000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC24
#check @N11Formalization.C450Source22GroupedC24.bound
#print axioms N11Formalization.C450Source22GroupedC24.valid0
#print axioms N11Formalization.C450Source22GroupedC24.valid1
#print axioms N11Formalization.C450Source22GroupedC24.valid2
#print axioms N11Formalization.C450Source22GroupedC24.valid3
#print axioms N11Formalization.C450Source22GroupedC24.valid4
#print axioms N11Formalization.C450Source22GroupedC24.valid5
#print axioms N11Formalization.C450Source22GroupedC24.valid6
#print axioms N11Formalization.C450Source22GroupedC24.valid7
#print axioms N11Formalization.C450Source22GroupedC24.valid8
#print axioms N11Formalization.C450Source22GroupedC24.valid9
#print axioms N11Formalization.C450Source22GroupedC24.valid10
#print axioms N11Formalization.C450Source22GroupedC24.bound
#print axioms N11Formalization.C450Source22GroupedC24.endpoint_checks
