import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6488911689:ℚ)/10000000000),((1677257491:ℚ)/2500000000),((-2311772473:ℚ)/12400000000),((-2008911689:ℚ)/20220000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1368867203:ℚ)/2500000000),((1207718210268967240917529197973613539:ℚ)/11916400000000000000000000000000000000),((53852732559780048656078917:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((206571093:ℚ)/312500000),((6830317699:ℚ)/10000000000),((-9610953097:ℚ)/50550000000),((-66571093:ℚ)/643750000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((5160541707:ℚ)/10000000000),((2613663397442996464842089426306711281386604004449151593:ℚ)/25228621362304687500000000000000000000000000000000000000),((47303133027668072386573:ℚ)/722000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6731538767:ℚ)/10000000000),((6890925683:ℚ)/10000000000),((-9792777049:ℚ)/51500000000),((-2251538767:ℚ)/20790000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2413673447:ℚ)/5000000000),((171187465745875033784676729161619003299577525106522761:ℚ)/1667369079589843750000000000000000000000000000000000000),((42974135629488064976536853:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((849016891:ℚ)/1250000000),((6951510647:ℚ)/10000000000),((-906775631:ℚ)/4725000000),((-289016891:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((581583233:ℚ)/1250000000),((1628723301406786923237842358110292102941149999548451:ℚ)/15697705078125000000000000000000000000000000000000000),((628487964295477142936237:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1713177173:ℚ)/2500000000),((1753018309:ℚ)/2500000000),((-2539054927:ℚ)/13112500000),((-593177173:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((223587603:ℚ)/500000000),((738495146510593571745238617628336737232567217167626567:ℚ)/7045414117431640625000000000000000000000000000000000000),((2341236945440383748989133:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((6913260099:ℚ)/10000000000),((1408469267:ℚ)/2000000000),((-2049407801:ℚ)/10585000000),((-2433260099:ℚ)/21265000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((4283809647:ℚ)/10000000000),((290141307687481243211122354761638216817651448846553803:ℚ)/2779610042871093750000000000000000000000000000000000000),((34683805769098467196586077:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((3471763843:ℚ)/5000000000),((884076759:ℚ)/1250000000),((-1292230277:ℚ)/6645312500),((-1231763843:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((4186906371:ℚ)/10000000000),((6012785516364570971920009293022670150475365871972857:ℚ)/57316051629930734634399414062500000000000000000000000),((8322775959783753343364573:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((3486894981:ℚ)/5000000000),((7102876519:ℚ)/10000000000),((-117175613:ℚ)/600000000),((-1246894981:ℚ)/10727500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((4087862927:ℚ)/10000000000),((213484436943916263730940636992870762082897923291951:ℚ)/2025000000000000000000000000000000000000000000000000),((7973815053129169648913197:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((7004047001:ℚ)/10000000000),((7133133751:ℚ)/10000000000),((-10519401253:ℚ)/53637500000),((-2524047001:ℚ)/21550000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((996629751:ℚ)/2500000000),((153259956975741195345226875620679718110867662125659469391:ℚ)/1446694595416259765625000000000000000000000000000000000000),((30496273246185929865989477:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3517149437:ℚ)/5000000000),((7193632851:ℚ)/10000000000),((-10700898553:ℚ)/53875000000),((-1277149437:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1941346833:ℚ)/5000000000),((52720055761713198822869983266693313291144928060088968673:ℚ)/488665716552734375000000000000000000000000000000000000000),((7273535350720165096213213:ℚ)/184832000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1418957481:ℚ)/2000000000),((290164477:ℚ)/400000000),((-435293431:ℚ)/2174000000),((-522957481:ℚ)/4386000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3666747281:ℚ)/10000000000),((655444474939785979928009140740400949380896928861997:ℚ)/6020463295312500000000000000000000000000000000000000),((1051217472905186849288197:ℚ)/29573120000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((894407013:ℚ)/1250000000),((731457151:ℚ)/1000000000),((-1106371453:ℚ)/5482500000),((-334407013:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3437986493:ℚ)/10000000000),((1315405973092542562168796440106403440127085354057159:ℚ)/11976157177734375000000000000000000000000000000000000),((366470850367510398213613:ℚ)/11552000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((3607852751:ℚ)/5000000000),((1487086851:ℚ)/2000000000),((-2285260553:ℚ)/11060000000),((-151983639:ℚ)/1250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((159682567:ℚ)/500000000),((68576269464188502359177828376032298987881911833950999:ℚ)/603972775000000000000000000000000000000000000000000000),((5153805627323019499987477:ℚ)/184832000000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((3668274209:ℚ)/5000000000),((3778112501:ℚ)/5000000000),((-5894337503:ℚ)/28125000000),((-1428274209:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((528142613:ℚ)/2000000000),((8017514036925923620549641029625836017809893205367499303:ℚ)/69522857666015625000000000000000000000000000000000000000),((3724881439018784358430837:ℚ)/184832000000000000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((7457320027:ℚ)/10000000000),((8038737421:ℚ)/10000000000),((-13236212263:ℚ)/57200000000),((-2977320027:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1940758533:ℚ)/10000000000),((58160095219888798622272529571946676093718186621147007541:ℚ)/438631050000000000000000000000000000000000000000000000000),((9133261497247562620986733:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((992470267:ℚ)/1250000000),((4260175107:ℚ)/5000000000),((-7340525321:ℚ)/30500000000),((-432470267:ℚ)/3240000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3051215253091822629140511562018327424303470389884115801:ℚ)/22166113281250000000000000000000000000000000000000000000),((779603:ℚ)/256000000)⟩
theorem valid15 : Valid source36 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((842131321:ℚ)/1000000000),((5220211797:ℚ)/5000000000),((-10220635391:ℚ)/32400000000),((-394131321:ℚ)/3200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3838567223334771103312327218185417560921467449964521317:ℚ)/19929037500000000000000000000000000000000000000000000000),((779603:ℚ)/256000000)⟩
theorem valid16 : Valid source36 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10341200127:ℚ)/10000000000),((713191819:ℚ)/500000000),((-1595575457:ℚ)/4000000000),((-5861200127:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((10846098228914396974557345071031701:ℚ)/40000000000000000000000000000000000),((779603:ℚ)/256000000)⟩
theorem valid17 : Valid source36 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source36 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((45:ℚ)/64) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC11
#check @N11Formalization.C450Source36GroupedC11.bound
#print axioms N11Formalization.C450Source36GroupedC11.valid0
#print axioms N11Formalization.C450Source36GroupedC11.valid1
#print axioms N11Formalization.C450Source36GroupedC11.valid2
#print axioms N11Formalization.C450Source36GroupedC11.valid3
#print axioms N11Formalization.C450Source36GroupedC11.valid4
#print axioms N11Formalization.C450Source36GroupedC11.valid5
#print axioms N11Formalization.C450Source36GroupedC11.valid6
#print axioms N11Formalization.C450Source36GroupedC11.valid7
#print axioms N11Formalization.C450Source36GroupedC11.valid8
#print axioms N11Formalization.C450Source36GroupedC11.valid9
#print axioms N11Formalization.C450Source36GroupedC11.valid10
#print axioms N11Formalization.C450Source36GroupedC11.valid11
#print axioms N11Formalization.C450Source36GroupedC11.valid12
#print axioms N11Formalization.C450Source36GroupedC11.valid13
#print axioms N11Formalization.C450Source36GroupedC11.valid14
#print axioms N11Formalization.C450Source36GroupedC11.valid15
#print axioms N11Formalization.C450Source36GroupedC11.valid16
#print axioms N11Formalization.C450Source36GroupedC11.valid17
#print axioms N11Formalization.C450Source36GroupedC11.bound
#print axioms N11Formalization.C450Source36GroupedC11.endpoint_checks
