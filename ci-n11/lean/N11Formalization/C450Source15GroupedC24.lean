import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((368812697:ℚ)/625000000),((1607775513:ℚ)/2500000000),((1033896293:ℚ)/2225000000),((1887775513:ℚ)/3100000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6817870661:ℚ)/10000000000),((14651276392290227660241:ℚ)/2475312500000000000000000),((-208052807487832308752053:ℚ)/902500000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1594339677:ℚ)/2500000000),((666916677:ℚ)/1000000000),((13240377739:ℚ)/27650000000),((778916677:ℚ)/1335000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1437804093:ℚ)/2500000000),((8014138262810799278719967937238063:ℚ)/3822612500000000000000000000000000000),((-33846820651762938862973:ℚ)/144400000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((413466647:ℚ)/625000000),((3394092387:ℚ)/5000000000),((1138088843:ℚ)/2343750000),((564870341:ℚ)/987500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1286670493:ℚ)/2500000000),((22974796818541863287517378116753:ℚ)/54931640625000000000000000000000000),((-853139945783269094022253:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((1683626181:ℚ)/2500000000),((6907193847:ℚ)/10000000000),((13865383267:ℚ)/28600000000),((8027193847:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2409466549:ℚ)/5000000000),((1057001609479745634515433019416469:ℚ)/4089800000000000000000000000000000000),((-3425864195829084554870933:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1713383371:ℚ)/2500000000),((1756548607:ℚ)/2500000000),((14073683597:ℚ)/29075000000),((2036548607:ℚ)/3575000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((893848337:ℚ)/2000000000),((246138465484125871597812284757433:ℚ)/2113389062500000000000000000000000000),((-214946619492866034837413:ℚ)/902500000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/16),((1:ℚ)/2),((435784569:ℚ)/625000000),((7085691663:ℚ)/10000000000),((3570491983:ℚ)/7328125000),((8205691663:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1022988809:ℚ)/2500000000),((-328294071901524354126691006856189:ℚ)/537014160156250000000000000000000000),((-3453050998261084820650853:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3516029813:ℚ)/5000000000),((446574183:ℚ)/625000000),((28772208691:ℚ)/59100000000),((516574183:ℚ)/916015625),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3890468841:ℚ)/10000000000),((-5778175639993897909619415716329939:ℚ)/8732025000000000000000000000000000000),((-211161953419758064887:ℚ)/881347656250000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((1772891007:ℚ)/2500000000),((7204680269:ℚ)/10000000000),((14490237049:ℚ)/29787500000),((2774893423:ℚ)/4925000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1839279663:ℚ)/5000000000),((-3142595376022227180697322443930727:ℚ)/4436475781250000000000000000000000000),((-3466298251897947832868557:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((7151066359:ℚ)/10000000000),((7264171733:ℚ)/10000000000),((58377464513:ℚ)/120100000000),((8384171733:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1727152319:ℚ)/5000000000),((-13546358737197003116379055040703693:ℚ)/18030012500000000000000000000000000000),((-3472913425458425371630493:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((7210566669:ℚ)/10000000000),((7383149203:ℚ)/10000000000),((58793966683:ℚ)/122000000000),((8503149203:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((803779497:ℚ)/2500000000),((-15755918866236334121685570355010373:ℚ)/74420000000000000000000000000000000000),((-3478855440963511224635533:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((7329561417:ℚ)/10000000000),((7502119677:ℚ)/10000000000),((59626929919:ℚ)/123900000000),((8622119677:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2675708767:ℚ)/10000000000),((-11177060577166543448671425178062553:ℚ)/38378025000000000000000000000000000000),((-3492046913934019414156973:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1862137159:ℚ)/2500000000),((7621083473:ℚ)/10000000000),((15114960113:ℚ)/31450000000),((2913694491:ℚ)/5162500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((499929387:ℚ)/2500000000),((-55178377889776558070094729704801:ℚ)/154547265625000000000000000000000000),((-184497936963911:ℚ)/760000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7567528669:ℚ)/10000000000),((1964748053:ℚ)/2500000000),((61292700683:ℚ)/129600000000),((2244748053:ℚ)/3931250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((18494517:ℚ)/200000000),((54947060773765858362754530913565491:ℚ)/83980800000000000000000000000000000000),((-741052985124701:ℚ)/3040000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((1951367111:ℚ)/2500000000),((9761561833:ℚ)/10000000000),((15739569777:ℚ)/40000000000),((10881561833:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((23657608768316556146314928897122731:ℚ)/2000000000000000000000000000000000000),((-976169:ℚ)/4000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((4854116537:ℚ)/5000000000),((3391143963:ℚ)/2500000000),((38138815759:ℚ)/110400000000),((3671143963:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((140671184872263338791583129:ℚ)/6094080000000000000000000000),((-976169:ℚ)/4000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC24
#check @N11Formalization.C450Source15GroupedC24.bound
#print axioms N11Formalization.C450Source15GroupedC24.valid0
#print axioms N11Formalization.C450Source15GroupedC24.valid1
#print axioms N11Formalization.C450Source15GroupedC24.valid2
#print axioms N11Formalization.C450Source15GroupedC24.valid3
#print axioms N11Formalization.C450Source15GroupedC24.valid4
#print axioms N11Formalization.C450Source15GroupedC24.valid5
#print axioms N11Formalization.C450Source15GroupedC24.valid6
#print axioms N11Formalization.C450Source15GroupedC24.valid7
#print axioms N11Formalization.C450Source15GroupedC24.valid8
#print axioms N11Formalization.C450Source15GroupedC24.valid9
#print axioms N11Formalization.C450Source15GroupedC24.valid10
#print axioms N11Formalization.C450Source15GroupedC24.valid11
#print axioms N11Formalization.C450Source15GroupedC24.valid12
#print axioms N11Formalization.C450Source15GroupedC24.valid13
#print axioms N11Formalization.C450Source15GroupedC24.valid14
#print axioms N11Formalization.C450Source15GroupedC24.bound
#print axioms N11Formalization.C450Source15GroupedC24.endpoint_checks
