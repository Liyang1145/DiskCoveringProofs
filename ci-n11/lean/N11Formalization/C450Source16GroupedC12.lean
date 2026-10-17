import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((6316244811:ℚ)/10000000000),((3299859891:ℚ)/5000000000),((-2403859891:ℚ)/9920000000),((-3916244811:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2948704149:ℚ)/5000000000),((2454689567802114662101124253066634317415703062894245787:ℚ)/41350753173828125000000000000000000000000000000000000000),((1431637016773485891206387:ℚ)/36480000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((3277312201:ℚ)/5000000000),((53422833:ℚ)/78125000),((-39422833:ℚ)/160937500),((-2077312201:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5307047551:ℚ)/10000000000),((282005019991149052987533247604847847708177571806025881:ℚ)/4786422824707031250000000000000000000000000000000000000),((107334290209760857691449:ℚ)/3040000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((1698235269:ℚ)/2500000000),((1739325061:ℚ)/2500000000),((-430441687:ℚ)/1780000000),((-1098235269:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2325150851:ℚ)/5000000000),((125948087542167541340184617027703051455759553812972427:ℚ)/2180262179698944091796875000000000000000000000000000000),((71509073999057095833467:ℚ)/2280000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((864009737:ℚ)/1250000000),((1754220867:ℚ)/2500000000),((-1306220867:ℚ)/5435000000),((-564009737:ℚ)/3426562500),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2143776391:ℚ)/5000000000),((958548333768135135075443360070041561350960850533807:ℚ)/16748093628063797950744628906250000000000000000000000),((5583961254644419306981:ℚ)/190000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1394328251:ℚ)/2000000000),((884557887:ℚ)/1250000000),((-660557887:ℚ)/2741250000),((-914328251:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4094969739:ℚ)/10000000000),((25879943474356579389425319369678486426854655050525509:ℚ)/452714163526611328125000000000000000000000000000000000),((13814469243420488596849:ℚ)/486400000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3515600681:ℚ)/5000000000),((7136039221:ℚ)/10000000000),((-5344039221:ℚ)/22120000000),((-2315600681:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3893445021:ℚ)/10000000000),((418007646329997482121058946410882164022780461021093439:ℚ)/7320385327605009078979492187500000000000000000000000000),((83336199083777337348089:ℚ)/3040000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7090758303:ℚ)/10000000000),((1798902983:ℚ)/2500000000),((-1350902983:ℚ)/5577500000),((-521195367:ℚ)/3125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((460188281:ℚ)/1250000000),((1185170555056786040365097950308736557319122736373911:ℚ)/20777806639671325683593750000000000000000000000000000),((963968098896672319648523:ℚ)/36480000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1787578039:ℚ)/2500000000),((1451036263:ℚ)/2000000000),((-1092636263:ℚ)/4500000000),((-1187578039:ℚ)/7090625000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3457234241:ℚ)/10000000000),((11902442819091604244070054265297940143714375077251:ℚ)/208883841794729232788085937500000000000000000000000),((19330964134095743197329:ℚ)/760000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7209863001:ℚ)/10000000000),((1462949491:ℚ)/2000000000),((-1104549491:ℚ)/4538000000),((-4809863001:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1609023343:ℚ)/5000000000),((18158472081693136801080671695927995350287493291562419551:ℚ)/318991619375000000000000000000000000000000000000000000000),((891788881827210117619547:ℚ)/36480000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7269410913:ℚ)/10000000000),((7374310431:ℚ)/10000000000),((-5582310431:ℚ)/22880000000),((-1623136971:ℚ)/9612500000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2960325261:ℚ)/10000000000),((22043577643568001637625221302601621094406677099919:ℚ)/387610167783498764038085937500000000000000000000000),((855675866209997872775243:ℚ)/36480000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((1832238991:ℚ)/2500000000),((3716935161:ℚ)/5000000000),((-2820935161:ℚ)/11535000000),((-1232238991:ℚ)/7268750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((107148811:ℚ)/400000000),((1310952535299436008340939362786724656368609709107468217:ℚ)/23072548436031341552734375000000000000000000000000000000),((17073899801236325660769:ℚ)/760000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((3694249113:ℚ)/5000000000),((1888245287:ℚ)/2500000000),((-1440245287:ℚ)/5815000000),((-831416371:ℚ)/4925000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2364708211:ℚ)/10000000000),((154984401714999159766068452669347162691772292238546391:ℚ)/2713491454772949218750000000000000000000000000000000000),((195850703341344174805643:ℚ)/9120000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7507574649:ℚ)/10000000000),((973896117:ℚ)/1250000000),((-749896117:ℚ)/2955000000),((-5107574649:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((780575427:ℚ)/5000000000),((25188524451029959979645804826451065157430017233211703971:ℚ)/436672431640625000000000000000000000000000000000000000000),((711066803257691830737947:ℚ)/36480000000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((2478623:ℚ)/3200000),((8267423037:ℚ)/10000000000),((-6475423037:ℚ)/24400000000),((-1710623:ℚ)/10368000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((103955842174990587948394452561374732944615823:ℚ)/1770449633280000000000000000000000000000000000),((2297799:ℚ)/128000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8221831473:ℚ)/10000000000),((10171244603:ℚ)/10000000000),((-8379244603:ℚ)/25920000000),((-5821831473:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((8709819504496264613321727334810815798143104212554946173:ℚ)/135000000000000000000000000000000000000000000000000000000),((2297799:ℚ)/128000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10125289177:ℚ)/10000000000),((6987862639:ℚ)/5000000000),((-6091862639:ℚ)/16000000000),((-7725289177:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((716622543736557087850772003132394708783695635973199493:ℚ)/9855270000000000000000000000000000000000000000000000000),((2297799:ℚ)/128000000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC12
#check @N11Formalization.C450Source16GroupedC12.bound
#print axioms N11Formalization.C450Source16GroupedC12.valid0
#print axioms N11Formalization.C450Source16GroupedC12.valid1
#print axioms N11Formalization.C450Source16GroupedC12.valid2
#print axioms N11Formalization.C450Source16GroupedC12.valid3
#print axioms N11Formalization.C450Source16GroupedC12.valid4
#print axioms N11Formalization.C450Source16GroupedC12.valid5
#print axioms N11Formalization.C450Source16GroupedC12.valid6
#print axioms N11Formalization.C450Source16GroupedC12.valid7
#print axioms N11Formalization.C450Source16GroupedC12.valid8
#print axioms N11Formalization.C450Source16GroupedC12.valid9
#print axioms N11Formalization.C450Source16GroupedC12.valid10
#print axioms N11Formalization.C450Source16GroupedC12.valid11
#print axioms N11Formalization.C450Source16GroupedC12.valid12
#print axioms N11Formalization.C450Source16GroupedC12.valid13
#print axioms N11Formalization.C450Source16GroupedC12.valid14
#print axioms N11Formalization.C450Source16GroupedC12.valid15
#print axioms N11Formalization.C450Source16GroupedC12.bound
#print axioms N11Formalization.C450Source16GroupedC12.endpoint_checks
