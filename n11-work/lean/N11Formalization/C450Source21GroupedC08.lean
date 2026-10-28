import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6544965529:ℚ)/10000000000),((342671463:ℚ)/500000000),((-2476043167:ℚ)/4960000000),((-4944965529:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1333025941:ℚ)/2500000000),((45463648983666363683460577020367340041292481214693082271:ℚ)/413507531738281250000000000000000000000000000000000000000),((3428298318293487884439453533:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6783765003:ℚ)/10000000000),((174319989:ℚ)/250000000),((-1264879901:ℚ)/2575000000),((-5183765003:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((935430651:ℚ)/2000000000),((38528946222311490581255197391483836222650099993832511221:ℚ)/362838827047729492187500000000000000000000000000000000000),((3354829736639747125731224517:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6903129159:ℚ)/10000000000),((1406495259:ℚ)/2000000000),((-10226457331:ℚ)/20980000000),((-5303129159:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((13486837:ℚ)/31250000),((1585805438676241074110935994561375790132385149431218810199:ℚ)/15186515286311340332031250000000000000000000000000000000000),((3317767011471663195733124253:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((6962802907:ℚ)/10000000000),((3546073811:ℚ)/5000000000),((-25834664299:ℚ)/52925000000),((-1787600969:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1031020227:ℚ)/2500000000),((30441849614716483628832214542269184141937766278536497317:ℚ)/291488158789062500000000000000000000000000000000000000000),((3299153422726129925347436837:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((70224713:ℚ)/100000000),((1430362737:ℚ)/2000000000),((-10441264633:ℚ)/21360000000),((-54224713:ℚ)/134687500),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3923596309:ℚ)/10000000000),((1663551625638655060259096832295747123659827313761:ℚ)/15926970986276865005493164062500000000000000000000),((328048497543911021051197:ℚ)/1478656000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7082134481:ℚ)/10000000000),((112679291:ℚ)/156250000),((-824113619:ℚ)/1683593750),((-5482134481:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((928226971:ℚ)/2500000000),((705873252482458182993882562216269463725821546979897769119:ℚ)/6757342917395019531250000000000000000000000000000000000000),((3261761639886050713095449293:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((714179259:ℚ)/1000000000),((7271130573:ℚ)/10000000000),((-53280175157:ℚ)/108700000000),((-554179259:ℚ)/1370625000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3490163457:ℚ)/10000000000),((50764044300651315421996370226176265333243122075933173:ℚ)/485918023128890991210937500000000000000000000000000000),((32429833867449623534647653:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((3600722879:ℚ)/5000000000),((3665390831:ℚ)/5000000000),((-26908517479:ℚ)/54825000000),((-2800722879:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((406610289:ℚ)/1250000000),((7390513085493491233018562270822251090575446990032303607:ℚ)/70736588051033020019531250000000000000000000000000000000),((806037547251963620670917933:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((1452218823:ℚ)/2000000000),((461901751:ℚ)/625000000),((-3397115759:ℚ)/6912500000),((-11672359:ℚ)/28750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2997609013:ℚ)/10000000000),((536366164510635971763675547962981538688810556687:ℚ)/5133324432373046875000000000000000000000000000000),((128210480779456186317835677:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((915092223:ℚ)/1250000000),((7450069757:ℚ)/10000000000),((-54890627813:ℚ)/111550000000),((-715092223:ℚ)/1757812500),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((679818843:ℚ)/2500000000),((30913421432927320895079137210953114243816082174099143:ℚ)/295840254693757742643356323242187500000000000000000000),((49786232073832337338568877:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((1476075377:ℚ)/2000000000),((378466993:ℚ)/500000000),((-2798202937:ℚ)/5625000000),((-1156075377:ℚ)/2860000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1204948987:ℚ)/5000000000),((139570146993814420083219565368662075089684834746210433:ℚ)/1315893150000000000000000000000000000000000000000000000),((126692826550368789777144077:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((3749820921:ℚ)/5000000000),((7807829591:ℚ)/10000000000),((-58110466319:ℚ)/114400000000),((-2949820921:ℚ)/7387500000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((325382061:ℚ)/2000000000),((1091280987130719556492605291146942342989392993784476223:ℚ)/10009353689575195312500000000000000000000000000000000000),((782289780953323203828392733:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((3869060893:ℚ)/5000000000),((1609251461:ℚ)/2000000000),((-12051263149:ℚ)/23640000000),((-3069060893:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((178177267606936561796496901709348945474012662260445127963:ℚ)/1637521618652343750000000000000000000000000000000000000000),((214464839:ℚ)/1024000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((997067541:ℚ)/1250000000),((4261474329:ℚ)/5000000000),((-32273268961:ℚ)/61000000000),((-797067541:ℚ)/2025000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((40046551580631332666092886477272577777007631525518881:ℚ)/351756738281250000000000000000000000000000000000000000),((214464839:ℚ)/1024000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((845321497:ℚ)/1000000000),((325878157:ℚ)/312500000),((-2552903413:ℚ)/4050000000),((-685321497:ℚ)/2000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((561362224329961504380377525620990914110901499471951777:ℚ)/4050000000000000000000000000000000000000000000000000000),((214464839:ℚ)/1024000000)⟩
theorem valid14 : Valid source21 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((10358316489:ℚ)/10000000000),((14234139439:ℚ)/10000000000),((-115947254951:ℚ)/160000000000),((-8758316489:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5121209733515687081606113865327135100918751329207027858932639:ℚ)/30470400000000000000000000000000000000000000000000000000000000),((214464839:ℚ)/1024000000)⟩
theorem valid15 : Valid source21 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC08
#check @N11Formalization.C450Source21GroupedC08.bound
#print axioms N11Formalization.C450Source21GroupedC08.valid0
#print axioms N11Formalization.C450Source21GroupedC08.valid1
#print axioms N11Formalization.C450Source21GroupedC08.valid2
#print axioms N11Formalization.C450Source21GroupedC08.valid3
#print axioms N11Formalization.C450Source21GroupedC08.valid4
#print axioms N11Formalization.C450Source21GroupedC08.valid5
#print axioms N11Formalization.C450Source21GroupedC08.valid6
#print axioms N11Formalization.C450Source21GroupedC08.valid7
#print axioms N11Formalization.C450Source21GroupedC08.valid8
#print axioms N11Formalization.C450Source21GroupedC08.valid9
#print axioms N11Formalization.C450Source21GroupedC08.valid10
#print axioms N11Formalization.C450Source21GroupedC08.valid11
#print axioms N11Formalization.C450Source21GroupedC08.valid12
#print axioms N11Formalization.C450Source21GroupedC08.valid13
#print axioms N11Formalization.C450Source21GroupedC08.valid14
#print axioms N11Formalization.C450Source21GroupedC08.valid15
#print axioms N11Formalization.C450Source21GroupedC08.bound
#print axioms N11Formalization.C450Source21GroupedC08.endpoint_checks
