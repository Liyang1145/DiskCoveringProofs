import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((3280584359:ℚ)/5000000000),((171810669:ℚ)/250000000),((-1226296021:ℚ)/2480000000),((-2440584359:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5290009889:ℚ)/10000000000),((12114715131486660667566965014337530075859968716186356749:ℚ)/77532662200927734375000000000000000000000000000000000000),((392001047006751530951095237:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((340005493:ℚ)/500000000),((6991861191:ℚ)/10000000000),((-50126750719:ℚ)/103000000000),((-256005493:ℚ)/655625000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4629223593:ℚ)/10000000000),((3430917660613470449687697498471797090907184447689973:ℚ)/22677426690483093261718750000000000000000000000000000),((3805498673490115303099373:ℚ)/18483200000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6919540937:ℚ)/10000000000),((1410313823:ℚ)/2000000000),((-10132824407:ℚ)/20980000000),((-5239540937:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((532983917:ℚ)/1250000000),((1131081843131692172964602794783848743308750144495334750199:ℚ)/7593257643155670166015625000000000000000000000000000000000),((1499056242918658218575666213:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((697924723:ℚ)/1000000000),((7111271067:ℚ)/10000000000),((-51201439603:ℚ)/105850000000),((-529924723:ℚ)/1335000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((813952093:ℚ)/2000000000),((586066438169531954516360033793954914054485131361150753:ℚ)/3935090143652343750000000000000000000000000000000000000),((14874243382426050295104733:ℚ)/73932800000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((351947379:ℚ)/500000000),((7170967207:ℚ)/10000000000),((-51738704863:ℚ)/106800000000),((-267947379:ℚ)/673437500),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((154660197:ℚ)/400000000),((74114382117909755359770579032819370442186718827163:ℚ)/497717843321152031421661376953125000000000000000000),((3689380532862431204513757:ℚ)/18483200000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7098642147:ℚ)/10000000000),((7230657689:ℚ)/10000000000),((-52275919201:ℚ)/107750000000),((-5418642147:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3652573723:ℚ)/10000000000),((503029080673073859194185067385503170936869061707161629851:ℚ)/3378671458697509765625000000000000000000000000000000000000),((1464039848534182166414858493:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7158331083:ℚ)/10000000000),((7290342661:ℚ)/10000000000),((-52813083949:ℚ)/108700000000),((-1826110361:ℚ)/4568750000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((856490659:ℚ)/2500000000),((12055559262571489430870428909998349752349012757987582089:ℚ)/80986337188148498535156250000000000000000000000000000000),((1452287226451905484644883053:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7218014537:ℚ)/10000000000),((7350022267:ℚ)/10000000000),((-53350200403:ℚ)/109650000000),((-5538014537:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((636792043:ℚ)/2000000000),((326451746737246872766435994809525951093543379920671663:ℚ)/2193382575225830078125000000000000000000000000000000000),((1440494329111198474203679013:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((1819423163:ℚ)/2500000000),((3704848323:ℚ)/5000000000),((-3849090701:ℚ)/7900000000),((-1399423163:ℚ)/3485937500),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1461370083:ℚ)/5000000000),((97263515556868757950864492548998751568683503075296559:ℚ)/653605832821875810623168945312500000000000000000000000),((89291321218930114837974413:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((1467473113:ℚ)/2000000000),((746936593:ℚ)/1000000000),((-5442429337:ℚ)/11155000000),((-1131473113:ℚ)/2812500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2636590611:ℚ)/10000000000),((270440853798846835242244680308752982263929821061329827:ℚ)/1817642524838447570800781250000000000000000000000000000),((156984780212345357255933:ℚ)/819200000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7397033409:ℚ)/10000000000),((7588689731:ℚ)/10000000000),((-55498207579:ℚ)/112500000000),((-5717033409:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((231628383:ℚ)/1000000000),((12399762853123202648836807454943567902823926887070689247:ℚ)/82243321875000000000000000000000000000000000000000000000),((1404873819060742600814726037:ℚ)/7393280000000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((7516354401:ℚ)/10000000000),((8065805031:ℚ)/10000000000),((-4599403483:ℚ)/8800000000),((-95677941:ℚ)/250000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((742504143:ℚ)/5000000000),((86987030006196156455915542770907043478753810132817:ℚ)/537109375000000000000000000000000000000000000000000),((1380925140759912260907013077:ℚ)/7393280000000000000000000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((3996729677:ℚ)/5000000000),((2135667693:ℚ)/2500000000),((-16021009237:ℚ)/30500000000),((-3156729677:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5424704098666114933604788008997582901176546170974839477:ℚ)/33768646875000000000000000000000000000000000000000000000),((94462483:ℚ)/512000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((1058789497:ℚ)/1250000000),((10448353663:ℚ)/10000000000),((-81235182967:ℚ)/129600000000),((-848789497:ℚ)/2500000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((764177317815280790269230313718656045663418326425917711:ℚ)/3955078125000000000000000000000000000000000000000000000),((94462483:ℚ)/512000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((1296996391:ℚ)/1250000000),((142550127:ℚ)/100000000),((-1154951143:ℚ)/1600000000),((-1086996391:ℚ)/3450000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3513287352238892314701531369904839036853013185076958289:ℚ)/15235200000000000000000000000000000000000000000000000000),((94462483:ℚ)/512000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC08
#check @N11Formalization.C450Source22GroupedC08.bound
#print axioms N11Formalization.C450Source22GroupedC08.valid0
#print axioms N11Formalization.C450Source22GroupedC08.valid1
#print axioms N11Formalization.C450Source22GroupedC08.valid2
#print axioms N11Formalization.C450Source22GroupedC08.valid3
#print axioms N11Formalization.C450Source22GroupedC08.valid4
#print axioms N11Formalization.C450Source22GroupedC08.valid5
#print axioms N11Formalization.C450Source22GroupedC08.valid6
#print axioms N11Formalization.C450Source22GroupedC08.valid7
#print axioms N11Formalization.C450Source22GroupedC08.valid8
#print axioms N11Formalization.C450Source22GroupedC08.valid9
#print axioms N11Formalization.C450Source22GroupedC08.valid10
#print axioms N11Formalization.C450Source22GroupedC08.valid11
#print axioms N11Formalization.C450Source22GroupedC08.valid12
#print axioms N11Formalization.C450Source22GroupedC08.valid13
#print axioms N11Formalization.C450Source22GroupedC08.valid14
#print axioms N11Formalization.C450Source22GroupedC08.bound
#print axioms N11Formalization.C450Source22GroupedC08.endpoint_checks
