import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5512616947:ℚ)/10000000000),((189674043:ℚ)/312500000),((74078786417:ℚ)/106800000000),((679022129:ℚ)/775000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3796309291:ℚ)/5000000000),((-3761918781986088238137248658521002289:ℚ)/25378884000000000000000000000000000000),((-1948906235682379248061247:ℚ)/5415000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1497393323:ℚ)/2500000000),((6308032843:ℚ)/10000000000),((19831326553:ℚ)/27650000000),((22444098529:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6630773011:ℚ)/10000000000),((-5583216943947714078235413758959871296960002497398228009:ℚ)/33029761132812500000000000000000000000000000000000000000),((-658217865610838261627330549:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((3113975037:ℚ)/5000000000),((6427240027:ℚ)/10000000000),((13657908469:ℚ)/18750000000),((3257388583:ℚ)/3950000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3051578569:ℚ)/5000000000),((-68176358995587608723540192107866110687359658756314191:ℚ)/381469726562500000000000000000000000000000000000000000),((-654649399486555324179196629:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((1269423227:ℚ)/2000000000),((327321597:ℚ)/500000000),((16651655497:ℚ)/22880000000),((1157964791:ℚ)/1406250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5823965911:ℚ)/10000000000),((-303667596188289173363199680400417207993740263821948019:ℚ)/1701356800000000000000000000000000000000000000000000000),((-4882786587522707302382927:ℚ)/13862400000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3233134153:ℚ)/5000000000),((833201167:ℚ)/1250000000),((42284475683:ℚ)/58150000000),((2939603501:ℚ)/3575000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5532433623:ℚ)/10000000000),((-13690987497891877268623037261429516059483585544265112139:ℚ)/76808483740234375000000000000000000000000000000000000000),((-28020442152950184180149:ℚ)/80000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6585407271:ℚ)/10000000000),((6784772919:ℚ)/10000000000),((28626493327:ℚ)/39400000000),((23874318757:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1306617213:ℚ)/2500000000),((-4252945464044420695827193103246470849223837388350617519:ℚ)/23891790625000000000000000000000000000000000000000000000),((-1931062934370076680743910983:ℚ)/5544960000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((838066709:ℚ)/1250000000),((6903923351:ℚ)/10000000000),((10898733799:ℚ)/15012500000),((24231770053:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1225835729:ℚ)/2500000000),((-939785091194992350357299398696098440639621576688541423:ℚ)/5286632083129882812500000000000000000000000000000000000),((-639948253645855791827536301:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((6823648109:ℚ)/10000000000),((27433833:ℚ)/39062500),((88500129199:ℚ)/122000000000),((384205996:ℚ)/469140625),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2279689797:ℚ)/5000000000),((-503674530987672435128994227972083439145005145502084743863:ℚ)/2837262500000000000000000000000000000000000000000000000000),((-29121373749790160393867:ℚ)/84609375000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((867843893:ℚ)/1250000000),((7142187193:ℚ)/10000000000),((1603754689:ℚ)/2212500000),((24946561579:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((261838677:ℚ)/625000000),((-27777304961060162333005443011832946110522773792819:ℚ)/156691741943359375000000000000000000000000000000000),((-632341228710103944589747149:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1412368661:ℚ)/2000000000),((7261301729:ℚ)/10000000000),((18224055271:ℚ)/25160000000),((25303905187:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3785813467:ℚ)/10000000000),((-14886206917664642343104546262785698133400703089767:ℚ)/84091894531250000000000000000000000000000000000000),((-628473584961734149730160541:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((3590462543:ℚ)/5000000000),((3749749297:ℚ)/5000000000),((46215087973:ℚ)/64800000000),((13009247891:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((834084719:ℚ)/2500000000),((-884691500383999206242865819723216093968204986164369301:ℚ)/5248800000000000000000000000000000000000000000000000000),((-155152503074686354885138109:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7419059349:ℚ)/10000000000),((1175484747:ℚ)/1250000000),((95049652839:ℚ)/160000000000),((3966454241:ℚ)/4050000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2186460831:ℚ)/10000000000),((-34215016569342039137760920347706253410351592354425187087:ℚ)/400000000000000000000000000000000000000000000000000000000),((-42745183:ℚ)/128000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((14916873:ℚ)/16000000),((13209011753:ℚ)/10000000000),((61863201:ℚ)/117760000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-3331660950432182163047557059:ℚ)/102064193536000000000000000000),((-42745183:ℚ)/128000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC28
#check @N11Formalization.C450Source23GroupedC28.bound
#print axioms N11Formalization.C450Source23GroupedC28.valid0
#print axioms N11Formalization.C450Source23GroupedC28.valid1
#print axioms N11Formalization.C450Source23GroupedC28.valid2
#print axioms N11Formalization.C450Source23GroupedC28.valid3
#print axioms N11Formalization.C450Source23GroupedC28.valid4
#print axioms N11Formalization.C450Source23GroupedC28.valid5
#print axioms N11Formalization.C450Source23GroupedC28.valid6
#print axioms N11Formalization.C450Source23GroupedC28.valid7
#print axioms N11Formalization.C450Source23GroupedC28.valid8
#print axioms N11Formalization.C450Source23GroupedC28.valid9
#print axioms N11Formalization.C450Source23GroupedC28.valid10
#print axioms N11Formalization.C450Source23GroupedC28.valid11
#print axioms N11Formalization.C450Source23GroupedC28.valid12
#print axioms N11Formalization.C450Source23GroupedC28.bound
#print axioms N11Formalization.C450Source23GroupedC28.endpoint_checks
