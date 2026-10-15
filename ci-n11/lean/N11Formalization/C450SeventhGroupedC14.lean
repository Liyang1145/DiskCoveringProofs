import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((6221823781:ℚ)/10000000000),((3357917891:ℚ)/5000000000),((-8473753673:ℚ)/49600000000),((-4301823781:ℚ)/53400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((38232549:ℚ)/62500000),((40608173862658396817747323370452486065169521253368364171:ℚ)/3687869081250000000000000000000000000000000000000000000000),((7822502131472632086002419:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6697049907:ℚ)/10000000000),((3417329307:ℚ)/5000000000),((-8651987921:ℚ)/53400000000),((-4777049907:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4924212359:ℚ)/10000000000),((1416243648000275343333264421901499014613717481444860563081:ℚ)/133955308320703125000000000000000000000000000000000000000000),((7238969762063278485428451:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((1363170299:ℚ)/2000000000),((6953478941:ℚ)/10000000000),((-17660436823:ℚ)/108700000000),((-979170299:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((458262363:ℚ)/1000000000),((2269468733516159303337794943658069413550633561902519791:ℚ)/215420102108203125000000000000000000000000000000000000000),((28429587297532166862088819:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((6934651309:ℚ)/10000000000),((3506444103:ℚ)/5000000000),((-8919332309:ℚ)/55300000000),((-5014651309:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4215541437:ℚ)/10000000000),((196062758833018079478542343555288871045752215090366145933:ℚ)/18740186438668823242187500000000000000000000000000000000000),((6966467030094770585922091:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((349702529:ℚ)/500000000),((7072296891:ℚ)/10000000000),((-18016890673:ℚ)/111550000000),((-253702529:ℚ)/2812500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4020268423:ℚ)/10000000000),((18987671355721528647579394011524657300570739737833837:ℚ)/1817642524838447570800781250000000000000000000000000000),((27603546068370094262024419:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((44084059:ℚ)/62500000),((1782926253:ℚ)/2500000000),((-4548778759:ℚ)/28125000000),((-32084059:ℚ)/354531250),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3815584353:ℚ)/10000000000),((16341683162302163698461685560649790460231905737:ℚ)/1566628813460469245910644531250000000000000000000),((1708847033854968869796691:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((71128479:ℚ)/100000000),((3595556291:ℚ)/5000000000),((-9186668873:ℚ)/56725000000),((-51928479:ℚ)/572000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3599880327:ℚ)/10000000000),((13822784757312886542445961991744915146123521527216491:ℚ)/1327005136600000000000000000000000000000000000000000000),((6769971870975660780653619:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-3:ℚ)/16),((-1:ℚ)/8),((7172245971:ℚ)/10000000000),((1444163233:ℚ)/2000000000),((-3692489699:ℚ)/22880000000),((-5252245971:ℚ)/57437500000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((842759353:ℚ)/2500000000),((879313553630920203872916425142196579978505214331314226037:ℚ)/84678400373077392578125000000000000000000000000000000000000),((1071945971172708811968411:ℚ)/73932800000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((7201944863:ℚ)/10000000000),((1450103923:ℚ)/2000000000),((-3710311769:ℚ)/22975000000),((-5281944863:ℚ)/57675000000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((81270669:ℚ)/250000000),((670042024507073237720034565510736106832782092953149131:ℚ)/64566854891492843627929687500000000000000000000000000000),((1066720899583292709722771:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7231643661:ℚ)/10000000000),((58479409:ℚ)/80000000),((-149838227:ℚ)/922800000),((-5311643661:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((625233419:ℚ)/2000000000),((14727411139261186279153236671626475073685048222070004639143:ℚ)/1417577375909765625000000000000000000000000000000000000000000),((1699682724404169876219:ℚ)/118292480000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((364552049:ℚ)/500000000),((7369332123:ℚ)/10000000000),((-18907996369:ℚ)/116300000000),((-268552049:ℚ)/2931250000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2861152421:ℚ)/10000000000),((2849394169490271126971456384136459006309656976057344569:ℚ)/274605714951324462890625000000000000000000000000000000000),((26296862619761424434385571:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3675218969:ℚ)/5000000000),((7428737623:ℚ)/10000000000),((-19086212869:ℚ)/117250000000),((-2715218969:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1284881641:ℚ)/5000000000),((32662013877683279176877317256528824100868323068205979967:ℚ)/3151476507128906250000000000000000000000000000000000000000),((26036510942927412477282571:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((3704917271:ℚ)/5000000000),((3773773587:ℚ)/5000000000),((-9721320761:ℚ)/59100000000),((-2744917271:ℚ)/30025000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2241732407:ℚ)/10000000000),((43271303375469278202518516846324604214784409248090991787:ℚ)/4165866081506347656250000000000000000000000000000000000000),((6454460305755891307298131:ℚ)/462080000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((301145069:ℚ)/400000000),((7666354869:ℚ)/10000000000),((-19799064607:ℚ)/120100000000),((-224345069:ℚ)/2440000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((54862611:ℚ)/400000000),((1695230781539210916777851476915860697876290848404397807:ℚ)/163562508600000000000000000000000000000000000000000000000),((531632231599013:ℚ)/38912000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7647417593:ℚ)/10000000000),((101769609:ℚ)/125000000),((-265308827:ℚ)/1525000000),((-5727417593:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((182183784751586702871678517942538692133439414039413110679:ℚ)/17289547200000000000000000000000000000000000000000000000000),((861869:ℚ)/64000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((8122569077:ℚ)/10000000000),((5021110433:ℚ)/5000000000),((-13463331299:ℚ)/64800000000),((-6202569077:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1439856896126939835174092545875155743287448778471400991253:ℚ)/129600000000000000000000000000000000000000000000000000000000),((861869:ℚ)/64000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((5011515527:ℚ)/5000000000),((13842986269:ℚ)/10000000000),((-38328958807:ℚ)/160000000000),((-176152849:ℚ)/2400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((396849329425086976741559917911318678504521122042627:ℚ)/32400000000000000000000000000000000000000000000000000),((861869:ℚ)/64000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((919:ℚ)/1280) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((1163:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC14
#check @N11Formalization.C450SeventhGroupedC14.bound
#print axioms N11Formalization.C450SeventhGroupedC14.valid0
#print axioms N11Formalization.C450SeventhGroupedC14.valid1
#print axioms N11Formalization.C450SeventhGroupedC14.valid2
#print axioms N11Formalization.C450SeventhGroupedC14.valid3
#print axioms N11Formalization.C450SeventhGroupedC14.valid4
#print axioms N11Formalization.C450SeventhGroupedC14.valid5
#print axioms N11Formalization.C450SeventhGroupedC14.valid6
#print axioms N11Formalization.C450SeventhGroupedC14.valid7
#print axioms N11Formalization.C450SeventhGroupedC14.valid8
#print axioms N11Formalization.C450SeventhGroupedC14.valid9
#print axioms N11Formalization.C450SeventhGroupedC14.valid10
#print axioms N11Formalization.C450SeventhGroupedC14.valid11
#print axioms N11Formalization.C450SeventhGroupedC14.valid12
#print axioms N11Formalization.C450SeventhGroupedC14.valid13
#print axioms N11Formalization.C450SeventhGroupedC14.valid14
#print axioms N11Formalization.C450SeventhGroupedC14.valid15
#print axioms N11Formalization.C450SeventhGroupedC14.valid16
#print axioms N11Formalization.C450SeventhGroupedC14.bound
#print axioms N11Formalization.C450SeventhGroupedC14.endpoint_checks
