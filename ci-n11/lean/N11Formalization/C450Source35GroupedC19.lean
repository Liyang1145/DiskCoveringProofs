import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/8),((3:ℚ)/16),((181230387:ℚ)/312500000),((6137874843:ℚ)/10000000000),((511230387:ℚ)/1609375000),((40173624529:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7027382183:ℚ)/10000000000),((-1663423281126485999661275914664778469252341453986327643567:ℚ)/6409366741943359375000000000000000000000000000000000000000),((-265746663425477929742066939:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6042367007:ℚ)/10000000000),((1564778469:ℚ)/2500000000),((16602367007:ℚ)/52450000000),((10134335407:ℚ)/25750000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((6517091363:ℚ)/10000000000),((-616781040890603993994515852908779835031519296877183688501047:ℚ)/2391833547898632812500000000000000000000000000000000000000000),((-17001551331177736970864771:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((246548403:ℚ)/400000000),((6380261647:ℚ)/10000000000),((222982801:ℚ)/712000000),((40900784941:ℚ)/104900000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((6249122077:ℚ)/10000000000),((-157906111441133333368433329649686545173408273590829400049:ℚ)/620598874055200000000000000000000000000000000000000000000),((-273976558711427922695956499:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1571239487:ℚ)/2500000000),((1625330783:ℚ)/2500000000),((4211239487:ℚ)/13587500000),((10315992349:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5971025867:ℚ)/10000000000),((-93585414184433771834653511623974096185484787269494667593461:ℚ)/372563201266955566406250000000000000000000000000000000000000),((-17242634433031359209517779:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((256244633:ℚ)/400000000),((3311151473:ℚ)/5000000000),((678644633:ℚ)/2212000000),((20813454419:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((142031867:ℚ)/250000000),((-309860333882323725832041729624000991457564382766092267593:ℚ)/1248862138621956250000000000000000000000000000000000000000),((-69435445842623640143048819:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6527188527:ℚ)/10000000000),((3371602691:ℚ)/5000000000),((1898576503:ℚ)/6250000000),((20994808073:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5377943551:ℚ)/10000000000),((-808191246919116922093184045656585519520389048524193039:ℚ)/3296136856079101562500000000000000000000000000000000000),((-69888906974177482758456491:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((6648180537:ℚ)/10000000000),((6864034431:ℚ)/10000000000),((17208180537:ℚ)/57200000000),((42352103293:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1011709597:ℚ)/2000000000),((-7656035069704573390959100127489928951668287740193817792419:ℚ)/31581435600000000000000000000000000000000000000000000000000),((-281323844398492442395507571:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((270763841:ℚ)/400000000),((1396958763:ℚ)/2000000000),((693163841:ℚ)/2326000000),((8542876289:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4719784533:ℚ)/10000000000),((-385668451825995371762810768064026786251110978240801684209:ℚ)/1608352444420150000000000000000000000000000000000000000000),((-11321863261734098899221659:ℚ)/36966400000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((55119511:ℚ)/80000000),((1421097401:ℚ)/2000000000),((139599511:ℚ)/472800000),((8615292203:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2178546539:ℚ)/5000000000),((-5889157587511974365542734999401123468565938943843427999:ℚ)/24818146831768800000000000000000000000000000000000000000),((-11388959113548990981147011:ℚ)/36966400000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((876339089:ℚ)/1250000000),((7346687563:ℚ)/10000000000),((2196339089:ℚ)/7625000000),((43800062689:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3963863497:ℚ)/10000000000),((-24848615219071582891465647289711193240738082480033758409089:ℚ)/107530586291503906250000000000000000000000000000000000000000),((-283692848932478668986458459:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((1813016667:ℚ)/2500000000),((3914211931:ℚ)/5000000000),((1484338889:ℚ)/5400000000),((22622635793:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1518788037:ℚ)/5000000000),((-29872748129786539896171783805963650336586238864735231003:ℚ)/135630450000000000000000000000000000000000000000000000000),((-3015288543844207:ℚ)/9728000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7734081609:ℚ)/10000000000),((9748870337:ℚ)/10000000000),((18294081609:ℚ)/80000000000),((51006611011:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-433960921488521834292120689026465856224068224859604264597249:ℚ)/2332800000000000000000000000000000000000000000000000000000000),((-8274347:ℚ)/25600000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9655369567:ℚ)/10000000000),((424147357:ℚ)/312500000),((20215369567:ℚ)/110400000000),((1952442071:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-108305732584387298234219993324483223398637478384466476189:ℚ)/700819200000000000000000000000000000000000000000000000000),((-8274347:ℚ)/25600000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC19
#check @N11Formalization.C450Source35GroupedC19.bound
#print axioms N11Formalization.C450Source35GroupedC19.valid0
#print axioms N11Formalization.C450Source35GroupedC19.valid1
#print axioms N11Formalization.C450Source35GroupedC19.valid2
#print axioms N11Formalization.C450Source35GroupedC19.valid3
#print axioms N11Formalization.C450Source35GroupedC19.valid4
#print axioms N11Formalization.C450Source35GroupedC19.valid5
#print axioms N11Formalization.C450Source35GroupedC19.valid6
#print axioms N11Formalization.C450Source35GroupedC19.valid7
#print axioms N11Formalization.C450Source35GroupedC19.valid8
#print axioms N11Formalization.C450Source35GroupedC19.valid9
#print axioms N11Formalization.C450Source35GroupedC19.valid10
#print axioms N11Formalization.C450Source35GroupedC19.valid11
#print axioms N11Formalization.C450Source35GroupedC19.valid12
#print axioms N11Formalization.C450Source35GroupedC19.bound
#print axioms N11Formalization.C450Source35GroupedC19.endpoint_checks
