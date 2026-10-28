import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((3170340889:ℚ)/5000000000),((6634390849:ℚ)/10000000000),((-4330390849:ℚ)/19840000000),((-1650340889:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2919670207:ℚ)/5000000000),((50997563936578515384925429460945780172582992025529119203:ℚ)/620261297607421875000000000000000000000000000000000000000),((928280921291432377416273:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6579641101:ℚ)/10000000000),((6873344429:ℚ)/10000000000),((-4569344429:ℚ)/20600000000),((-1179880367:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5241648057:ℚ)/10000000000),((4624692757023712543900931658962984176087599615907774831:ℚ)/56727974218750000000000000000000000000000000000000000000),((2111067710361699613718713:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3409247843:ℚ)/5000000000),((6992782773:ℚ)/10000000000),((-1562927591:ℚ)/7120000000),((-1889247843:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4574752807:ℚ)/10000000000),((55736814942901833671741437681250024857347864904181127517:ℚ)/697683897503662109375000000000000000000000000000000000000),((347727348512276861217:ℚ)/160000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1734471793:ℚ)/2500000000),((7112197269:ℚ)/10000000000),((-4808197269:ℚ)/21740000000),((-974471793:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((420512383:ℚ)/1000000000),((1396278734465467827577247206279257608581560218492856009:ℚ)/17530932788753509521484375000000000000000000000000000000),((-19060114011440794487063:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1411451289:ℚ)/2000000000),((3585947979:ℚ)/5000000000),((-2433947979:ℚ)/11060000000),((-803451289:ℚ)/5577500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((760421873:ℚ)/2000000000),((1478937917122912996968363509300005053887768637056722127:ℚ)/18740186438668823242187500000000000000000000000000000000),((-133654632826177422544381:ℚ)/27724800000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7116933111:ℚ)/10000000000),((451974321:ℚ)/625000000),((-3174993:ℚ)/14375000),((-4076933111:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3584589991:ℚ)/10000000000),((1476958316815401364542880823361730542559878944790021061:ℚ)/18738582730293273925781250000000000000000000000000000000),((-4556577325042363657809181:ℚ)/693120000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7176604643:ℚ)/10000000000),((1837739879:ℚ)/2500000000),((-1261739879:ℚ)/5625000000),((-4136604643:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1676827453:ℚ)/5000000000),((52121605444198772330310825421744232553750355330891423477:ℚ)/657946575000000000000000000000000000000000000000000000000),((-1924368736053498289308263:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((291837313:ℚ)/400000000),((7470309471:ℚ)/10000000000),((-5166309471:ℚ)/22880000000),((-170237313:ℚ)/1163000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2838256749:ℚ)/10000000000),((4273396287880510799881244272775528654519300440351197:ℚ)/54073172553125000000000000000000000000000000000000000),((-4378733479932857323503:ℚ)/369664000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7415241981:ℚ)/10000000000),((7589639997:ℚ)/10000000000),((-5285639997:ℚ)/23260000000),((-4375241981:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1104749009:ℚ)/5000000000),((68472460351030732188352094488499949827812180450416161371:ℚ)/868317265527343750000000000000000000000000000000000000000),((-10652440448839837861021621:ℚ)/693120000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((3767266519:ℚ)/5000000000),((313129857:ℚ)/400000000),((-73656619:ℚ)/315200000),((-2247266519:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((328376109:ℚ)/2500000000),((521421979842392765720044385157388476091037980485785781991:ℚ)/6550086474609375000000000000000000000000000000000000000000),((-1091672337756246119508207:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((7773064267:ℚ)/10000000000),((8305263401:ℚ)/10000000000),((-6001263401:ℚ)/24400000000),((-1577688089:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6481491621866480170714155892669501336995560505284133497:ℚ)/80044200000000000000000000000000000000000000000000000000),((-2667727:ℚ)/128000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((1649988847:ℚ)/2000000000),((10211406271:ℚ)/10000000000),((-7907406271:ℚ)/25920000000),((-1041988847:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((11507191817269389454488238499366427677845824339002209097:ℚ)/129600000000000000000000000000000000000000000000000000000),((-2667727:ℚ)/128000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10155670401:ℚ)/10000000000),((14018603233:ℚ)/10000000000),((-11714603233:ℚ)/32000000000),((-7115670401:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((39503545646545798336471912135950958542289539225426005117:ℚ)/394210800000000000000000000000000000000000000000000000000),((-2667727:ℚ)/128000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC12
#check @N11Formalization.C450Source20GroupedC12.bound
#print axioms N11Formalization.C450Source20GroupedC12.valid0
#print axioms N11Formalization.C450Source20GroupedC12.valid1
#print axioms N11Formalization.C450Source20GroupedC12.valid2
#print axioms N11Formalization.C450Source20GroupedC12.valid3
#print axioms N11Formalization.C450Source20GroupedC12.valid4
#print axioms N11Formalization.C450Source20GroupedC12.valid5
#print axioms N11Formalization.C450Source20GroupedC12.valid6
#print axioms N11Formalization.C450Source20GroupedC12.valid7
#print axioms N11Formalization.C450Source20GroupedC12.valid8
#print axioms N11Formalization.C450Source20GroupedC12.valid9
#print axioms N11Formalization.C450Source20GroupedC12.valid10
#print axioms N11Formalization.C450Source20GroupedC12.valid11
#print axioms N11Formalization.C450Source20GroupedC12.valid12
#print axioms N11Formalization.C450Source20GroupedC12.bound
#print axioms N11Formalization.C450Source20GroupedC12.endpoint_checks
