import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((87717911:ℚ)/125000000),((3589687501:ℚ)/5000000000),(-1:ℚ),((-226353733:ℚ)/250375000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((985224519:ℚ)/2500000000),((1677461980799757888339852649379:ℚ)/6268764062500000000000000000000),((146727074361045769209043:ℚ)/144400000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((161:ℚ)/256),(-1:ℚ),((-15:ℚ)/16),((3538439873:ℚ)/5000000000),((3604531251:ℚ)/5000000000),(-1:ℚ),((-1306188517:ℚ)/1437500000),((4973408481:ℚ)/5000000000),((62276473:ℚ)/62500000),((128974617:ℚ)/1250000000),((3731918187:ℚ)/10000000000),((683375461073735104109547709055537:ℚ)/2583007812500000000000000000000000),((441047856927463207627129:ℚ)/433200000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((2003:ℚ)/3200) ((161:ℚ)/256) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((161:ℚ)/256),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((710660267:ℚ)/1000000000),((3619375001:ℚ)/5000000000),(-1:ℚ),((-1837580801:ℚ)/2022000000),((9929701407:ℚ)/10000000000),((9946816967:ℚ)/10000000000),((18538009:ℚ)/156250000),((3623135981:ℚ)/10000000000),((900901834393934870548772112419117:ℚ)/3407070000000000000000000000000000),((147305142988789728584043:ℚ)/144400000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((161:ℚ)/256) ((1011:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7136325259:ℚ)/10000000000),((3634218751:ℚ)/5000000000),(-1:ℚ),((-18464975777:ℚ)/20315000000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((3511139311:ℚ)/10000000000),((136334852179943024775820890041045363:ℚ)/515874031250000000000000000000000000),((147594646399951747334043:ℚ)/144400000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4063:ℚ)/6400),((1629:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((7166047521:ℚ)/10000000000),((1820820313:ℚ)/2500000000),(-1:ℚ),((-18554142563:ℚ)/20362500000),((619036701:ℚ)/625000000),((9912884763:ℚ)/10000000000),((1382497003:ℚ)/10000000000),((3395609579:ℚ)/10000000000),((45402873872915859322644152297586287:ℚ)/172763085937500000000000000000000000),((36934878844963816618667:ℚ)/36100000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((4063:ℚ)/6400) ((1629:ℚ)/2560) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1629:ℚ)/2560),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7180908529:ℚ)/10000000000),((3649062501:ℚ)/5000000000),(-1:ℚ),((-1430671199:ℚ)/1570000000),((247409071:ℚ)/250000000),((9904587221:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((3336405401:ℚ)/10000000000),((40476729511435174837864663866203:ℚ)/154056250000000000000000000000000),((443653387627921376377129:ℚ)/433200000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1629:ℚ)/2560) ((2041:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2041:ℚ)/3200),((8183:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3597884729:ℚ)/5000000000),((457060547:ℚ)/625000000),(-1:ℚ),((-9321654187:ℚ)/10228750000),((9888211123:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((37416203:ℚ)/250000000),((3276172501:ℚ)/10000000000),((8413196231686443898473381582166129:ℚ)/32028773437500000000000000000000000),((2312960748254801941987:ℚ)/2256250000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8183:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8183:ℚ)/12800),((4101:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3605315153:ℚ)/5000000000),((3663906251:ℚ)/5000000000),(-1:ℚ),((-9343945459:ℚ)/10252500000),((4940065779:ℚ)/5000000000),((1236026391:ℚ)/1250000000),((774947369:ℚ)/5000000000),((3214853001:ℚ)/10000000000),((11501766618923328546662111644904369:ℚ)/43797398437500000000000000000000000),((148174591416855862959043:ℚ)/144400000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((8183:ℚ)/12800) ((4101:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((289019643:ℚ)/400000000),((1835664063:ℚ)/2500000000),(-1:ℚ),((-749298929:ℚ)/822100000),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((630476683:ℚ)/2000000000),((11090266251840165570243886924413:ℚ)/42240525625000000000000000000000),((111239829846214556106001:ℚ)/108300000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((1448070353:ℚ)/2000000000),((3678750001:ℚ)/5000000000),(-1:ℚ),((-3755411059:ℚ)/4120000000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((772173473:ℚ)/2500000000),((11138953936845885797422973588327403:ℚ)/42436000000000000000000000000000000),((148465033022597959834043:ℚ)/144400000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7255212377:ℚ)/10000000000),((921542969:ℚ)/1250000000),(-1:ℚ),((-18821637131:ℚ)/20647500000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((3023707269:ℚ)/10000000000),((93231324773658587454860398701580891:ℚ)/355266046875000000000000000000000000),((9288148193736969877323:ℚ)/9025000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((454379557:ℚ)/625000000),((3693593751:ℚ)/5000000000),(-1:ℚ),((-1179138671:ℚ)/1293437500),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((2957337961:ℚ)/10000000000),((1755731456663960650592922466922137:ℚ)/6691922265625000000000000000000000),((446267362079600248252129:ℚ)/433200000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7284933369:ℚ)/10000000000),((1850507813:ℚ)/2500000000),(-1:ℚ),((-18910800107:ℚ)/20742500000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((1444745311:ℚ)/5000000000),((282143023930232718863806131257888639:ℚ)/1075628265625000000000000000000000000),((37225320450705913493667:ℚ)/36100000000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7299793749:ℚ)/10000000000),((3708437501:ℚ)/5000000000),(-1:ℚ),((-1723216477:ℚ)/1890000000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((2820058497:ℚ)/10000000000),((18586642139412247411487810267879:ℚ)/70875000000000000000000000000000),((149046854428662231709043:ℚ)/144400000000000000000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7314654053:ℚ)/10000000000),((3723281251:ℚ)/5000000000),(-1:ℚ),((-18999962159:ℚ)/20885000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((1374460709:ℚ)/5000000000),((143655846284345064358077541779528023:ℚ)/545229031250000000000000000000000000),((149338234228984406709043:ℚ)/144400000000000000000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1836093609:ℚ)/2500000000),((3738125001:ℚ)/5000000000),(-1:ℚ),((-4772280827:ℚ)/5245000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1300484601:ℚ)/5000000000),((9056035481293373302863065074484459:ℚ)/34387531250000000000000000000000000),((448889780282499823252129:ℚ)/433200000000000000000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((184352363:ℚ)/250000000),((3767812501:ℚ)/5000000000),(-1:ℚ),((-479457089:ℚ)/529250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2444292967:ℚ)/10000000000),((372187396658216538606610050078879:ℚ)/1400527812500000000000000000000000),((150214250019111087959043:ℚ)/144400000000000000000000)⟩
theorem valid16 : Valid source24 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((7433533809:ℚ)/10000000000),((3797500001:ℚ)/5000000000),(-1:ℚ),((-19356601427:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((209684891:ℚ)/1000000000),((151403733820208740619818768435140157:ℚ)/570312000000000000000000000000000000),((150799824203495672334043:ℚ)/144400000000000000000000)⟩
theorem valid17 : Valid source24 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((7492971953:ℚ)/10000000000),((3916250001:ℚ)/5000000000),(-1:ℚ),((-19534915859:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((420056781:ℚ)/2500000000),((231560454339562281453281396003449:ℚ)/829500000000000000000000000000000),((522331:ℚ)/500000)⟩
theorem valid18 : Valid source24 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((120792401:ℚ)/156250000),((8070000003:ℚ)/10000000000),(-1:ℚ),((-316377203:ℚ)/357500000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((88683208278128858204305800788247:ℚ)/319515625000000000000000000000000),((522331:ℚ)/500000)⟩
theorem valid19 : Valid source24 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((1593687859:ℚ)/2000000000),((4510000001:ℚ)/5000000000),(-1:ℚ),((-4192263577:ℚ)/5184000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((21353461352452056248798356376271263:ℚ)/67184640000000000000000000000000000),((522331:ℚ)/500000)⟩
theorem valid20 : Valid source24 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((8919209347:ℚ)/10000000000),((5460000001:ℚ)/5000000000),(-1:ℚ),((-23813628041:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2653334617941149716567603894126289039:ℚ)/7680000000000000000000000000000000000),((522331:ℚ)/500000)⟩
theorem valid21 : Valid source24 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((2705077537:ℚ)/2500000000),((14720000003:ℚ)/10000000000),(-1:ℚ),((-7379232611:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((11827959592819245689465153:ℚ)/30470400000000000000000000),((522331:ℚ)/500000)⟩
theorem valid22 : Valid source24 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((161:ℚ)/256) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((1011:ℚ)/1600) ((1629:ℚ)/2560) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source24 nn0 nn1 Qcell ((161:ℚ)/256) ((1629:ℚ)/2560) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1629:ℚ)/2560) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source24 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source24 nn0 nn1 Qcell ((1629:ℚ)/2560) ((4101:ℚ)/6400) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source24 nn0 nn1 Qcell ((8221:ℚ)/12800) ((8259:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source24 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8259:ℚ)/12800) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source24 nn0 nn1 Qcell ((1629:ℚ)/2560) ((8259:ℚ)/12800) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((8259:ℚ)/12800) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source24 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source24 nn0 nn1 Qcell ((8259:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source24 nn0 nn1 Qcell ((4177:ℚ)/6400) ((2117:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source24 nn0 nn1 Qcell ((8259:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source24 nn0 nn1 Qcell ((8259:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC01
#check @N11Formalization.C450Source24GroupedC01.bound
#print axioms N11Formalization.C450Source24GroupedC01.valid0
#print axioms N11Formalization.C450Source24GroupedC01.valid1
#print axioms N11Formalization.C450Source24GroupedC01.valid2
#print axioms N11Formalization.C450Source24GroupedC01.valid3
#print axioms N11Formalization.C450Source24GroupedC01.valid4
#print axioms N11Formalization.C450Source24GroupedC01.valid5
#print axioms N11Formalization.C450Source24GroupedC01.valid6
#print axioms N11Formalization.C450Source24GroupedC01.valid7
#print axioms N11Formalization.C450Source24GroupedC01.valid8
#print axioms N11Formalization.C450Source24GroupedC01.valid9
#print axioms N11Formalization.C450Source24GroupedC01.valid10
#print axioms N11Formalization.C450Source24GroupedC01.valid11
#print axioms N11Formalization.C450Source24GroupedC01.valid12
#print axioms N11Formalization.C450Source24GroupedC01.valid13
#print axioms N11Formalization.C450Source24GroupedC01.valid14
#print axioms N11Formalization.C450Source24GroupedC01.valid15
#print axioms N11Formalization.C450Source24GroupedC01.valid16
#print axioms N11Formalization.C450Source24GroupedC01.valid17
#print axioms N11Formalization.C450Source24GroupedC01.valid18
#print axioms N11Formalization.C450Source24GroupedC01.valid19
#print axioms N11Formalization.C450Source24GroupedC01.valid20
#print axioms N11Formalization.C450Source24GroupedC01.valid21
#print axioms N11Formalization.C450Source24GroupedC01.valid22
#print axioms N11Formalization.C450Source24GroupedC01.bound
#print axioms N11Formalization.C450Source24GroupedC01.endpoint_checks
