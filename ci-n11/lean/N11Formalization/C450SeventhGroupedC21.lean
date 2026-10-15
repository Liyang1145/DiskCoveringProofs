import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((6120807047:ℚ)/10000000000),((3311095211:ℚ)/5000000000),((6920807047:ℚ)/26700000000),((3695095211:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6344980371:ℚ)/10000000000),((57498379296351245990578670335642334143:ℚ)/8698964373504000000000000000000000000000),((-1720204631515031655008049:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6596105603:ℚ)/10000000000),((6859786993:ℚ)/10000000000),((7396105603:ℚ)/27650000000),((7627786993:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((64977493:ℚ)/125000000),((166390409034306654868521229538854981395243653076052018708589:ℚ)/27939928093761600000000000000000000000000000000000000000000000),((-1758392037130761817175449:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((6833739481:ℚ)/10000000000),((697858283:ℚ)/1000000000),((2544579827:ℚ)/9375000000),((110665469:ℚ)/316000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4529129583:ℚ)/10000000000),((5038431831995472134988778004882110659963286311739:ℚ)/887470200000000000000000000000000000000000000000000),((-4924215138643884395761:ℚ)/80000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((3476276513:ℚ)/5000000000),((7037980173:ℚ)/10000000000),((3876276513:ℚ)/14181250000),((2601993391:ℚ)/7500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4157600577:ℚ)/10000000000),((37663213966291581317683347615806913297354375055496322663169:ℚ)/6787389990234375000000000000000000000000000000000000000000000),((-446826372871663225475359:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((7011958999:ℚ)/10000000000),((887172143:ℚ)/1250000000),((600919923:ℚ)/2200000000),((983172143:ℚ)/2836250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1979806991:ℚ)/5000000000),((173223498596873505856745075532945709643843950706213:ℚ)/31371567919677734375000000000000000000000000000000000),((-1792147161165466924423761:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((3535682229:ℚ)/5000000000),((7156773753:ℚ)/10000000000),((3935682229:ℚ)/14418750000),((609597981:ℚ)/1760000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3751772329:ℚ)/10000000000),((41525349556875743565260904623060431948420456239903449873:ℚ)/7556174313600000000000000000000000000000000000000000000000),((-1347746502351077048285053:ℚ)/21660000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3565384707:ℚ)/5000000000),((7216170009:ℚ)/10000000000),((3965384707:ℚ)/14537500000),((2661390003:ℚ)/7690000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((706466483:ℚ)/2000000000),((420614189655963782601673868279434885241711088581998264573:ℚ)/76886211484815125000000000000000000000000000000000000000000),((-1351387513593114093944017:ℚ)/21660000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/4),((5:ℚ)/16),((7190173881:ℚ)/10000000000),((45472287:ℚ)/62500000),((7990173881:ℚ)/29312500000),((50272287:ℚ)/145375000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3298976309:ℚ)/10000000000),((2875719486857445217738139716501834902101337161968057:ℚ)/527964715374552917480468750000000000000000000000000000),((-5420133621341157898751563:ℚ)/86640000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((724957787:ℚ)/1000000000),((1466992299:ℚ)/2000000000),((804957787:ℚ)/2955000000),((1620592299:ℚ)/4690000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((38106317:ℚ)/125000000),((152690496202571904819036744585132748999092331768369232101:ℚ)/28150331938460156250000000000000000000000000000000000000000),((-50182241112938774219:ℚ)/800000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((7308981393:ℚ)/10000000000),((3697178371:ℚ)/5000000000),((8108981393:ℚ)/29787500000),((4081178371:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((555257253:ℚ)/2000000000),((474970375384381453912822194515159361496800325196417835834647:ℚ)/87916783500893925000000000000000000000000000000000000000000000),((-5449359330424521796947067:ℚ)/86640000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((7368384461:ℚ)/10000000000),((1863437917:ℚ)/2500000000),((8168384461:ℚ)/30025000000),((2055437917:ℚ)/5957500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((618787063:ℚ)/2500000000),((320587997327759996189328058540364368494616649746568947763:ℚ)/59567339989394186401367187500000000000000000000000000000000),((-1821333825757289317572481:ℚ)/28880000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((1856946771:ℚ)/2500000000),((7572540589:ℚ)/10000000000),((2056946771:ℚ)/7625000000),((8340540589:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2132870899:ℚ)/10000000000),((874320692611656235511498170609025383806101191009766686139:ℚ)/161149402983025000000000000000000000000000000000000000000000),((-85604111798309807390857:ℚ)/1353750000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7546591039:ℚ)/10000000000),((8047684857:ℚ)/10000000000),((2782197013:ℚ)/10800000000),((8815684857:ℚ)/24400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((593116401:ℚ)/5000000000),((47475770656277367138599114050269089654495098138290729007:ℚ)/8273457450000000000000000000000000000000000000000000000000),((-1836015037593464091176481:ℚ)/28880000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((8021791029:ℚ)/10000000000),((9948124827:ℚ)/10000000000),((8821791029:ℚ)/40000000000),((3572041609:ℚ)/8640000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2511000544478411479534634985976735701572097304361453:ℚ)/377913600000000000000000000000000000000000000000000000),((-1631403:ℚ)/25600000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((992240091:ℚ)/1000000000),((343716031:ℚ)/250000000),((1072240091:ℚ)/5520000000),((362916031:ℚ)/800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2559771965072425661599726672885627:ℚ)/304704000000000000000000000000000000),((-1631403:ℚ)/25600000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC21
#check @N11Formalization.C450SeventhGroupedC21.bound
#print axioms N11Formalization.C450SeventhGroupedC21.valid0
#print axioms N11Formalization.C450SeventhGroupedC21.valid1
#print axioms N11Formalization.C450SeventhGroupedC21.valid2
#print axioms N11Formalization.C450SeventhGroupedC21.valid3
#print axioms N11Formalization.C450SeventhGroupedC21.valid4
#print axioms N11Formalization.C450SeventhGroupedC21.valid5
#print axioms N11Formalization.C450SeventhGroupedC21.valid6
#print axioms N11Formalization.C450SeventhGroupedC21.valid7
#print axioms N11Formalization.C450SeventhGroupedC21.valid8
#print axioms N11Formalization.C450SeventhGroupedC21.valid9
#print axioms N11Formalization.C450SeventhGroupedC21.valid10
#print axioms N11Formalization.C450SeventhGroupedC21.valid11
#print axioms N11Formalization.C450SeventhGroupedC21.valid12
#print axioms N11Formalization.C450SeventhGroupedC21.valid13
#print axioms N11Formalization.C450SeventhGroupedC21.valid14
#print axioms N11Formalization.C450SeventhGroupedC21.bound
#print axioms N11Formalization.C450SeventhGroupedC21.endpoint_checks
