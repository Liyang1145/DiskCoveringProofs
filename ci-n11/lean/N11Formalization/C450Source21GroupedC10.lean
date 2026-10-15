import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6444839687:ℚ)/10000000000),((6747179557:ℚ)/10000000000),((-35070256899:ℚ)/99200000000),((-12934519061:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5585862627:ℚ)/10000000000),((2992233420102924433286374866056509413136231565930227765659:ℚ)/26464482031250000000000000000000000000000000000000000000000),((185146553685684212630803351:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6683830457:ℚ)/10000000000),((3433332169:ℚ)/5000000000),((-17953325183:ℚ)/51500000000),((-13651491371:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1240219889:ℚ)/2500000000),((2552821889825401811585742310404850747025994260066526210453:ℚ)/23221684931054687500000000000000000000000000000000000000000),((172093868508370408281678871:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((425205311:ℚ)/625000000),((6986122741:ℚ)/10000000000),((-36742859187:ℚ)/104900000000),((-875615933:ℚ)/3337500000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((184794377:ℚ)/400000000),((742812989192585568210556845364496997721404870988454173:ℚ)/6770438973999023437500000000000000000000000000000000000),((646601363834045076745159:ℚ)/7220000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1730678553:ℚ)/2500000000),((1421111233:ℚ)/2000000000),((-7515778631:ℚ)/21360000000),((-3592035659:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2126882267:ℚ)/5000000000),((458421802402198085233890265195320283330954668835487842577:ℚ)/4186103385021972656250000000000000000000000000000000000000),((9933805899232461712122711:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7042119507:ℚ)/10000000000),((89565799:ℚ)/125000000),((-474960593:ℚ)/1358750000),((-14726358521:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((771084381:ℚ)/2000000000),((3363014005954155150811501555561063344544468027160248336207:ℚ)/31098753480249023437500000000000000000000000000000000000000),((152326646604176283472960671:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7101813569:ℚ)/10000000000),((903120739:ℚ)/1250000000),((-4801845173:ℚ)/13706250000),((-14905440707:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3640873167:ℚ)/10000000000),((3913800634570791933219614913425036068784601126265833857459:ℚ)/36217133082128906250000000000000000000000000000000000000000),((149010058487666709154725319:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3580751053:ℚ)/5000000000),((455291393:ℚ)/625000000),((-2427039751:ℚ)/6912500000),((-7542253159:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((213345039:ℚ)/625000000),((505950258938828287450132252065242132565500602607214719887:ℚ)/4685046609667205810546875000000000000000000000000000000000),((36421788089591185617487711:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7221185261:ℚ)/10000000000),((3672176597:ℚ)/5000000000),((-19625236179:ℚ)/55775000000),((-15263555783:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((126824237:ℚ)/400000000),((1046213449178628105086268019470345336738805563768771470873:ℚ)/9694093465805053710937500000000000000000000000000000000000),((142357922071162275882505759:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((1820215793:ℚ)/2500000000),((3731859571:ℚ)/5000000000),((-20043016997:ℚ)/56250000000),((-3860647379:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2908226523:ℚ)/10000000000),((17925088002921282325407652832469207931862060311044493339:ℚ)/164486643750000000000000000000000000000000000000000000000),((8688897606065540837088871:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7400203789:ℚ)/10000000000),((1540478239:ℚ)/2000000000),((-8351347673:ℚ)/22880000000),((-15800611367:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((114902077:ℚ)/500000000),((568652199824415229026258150267081801044879416658572563809:ℚ)/5124789089062500000000000000000000000000000000000000000000),((132332228069259944493339359:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((7638827657:ℚ)/10000000000),((7940989727:ℚ)/10000000000),((-43426928089:ℚ)/118200000000),((-16516482971:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((92709038574234822132926583085349702854803178188543763199549:ℚ)/838411068750000000000000000000000000000000000000000000000000),((335381:ℚ)/5120000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((7877381047:ℚ)/10000000000),((4208996159:ℚ)/5000000000),((-23382973113:ℚ)/61000000000),((-17232143141:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1313925495367306636857858270777858278793176345567307457681:ℚ)/11526364800000000000000000000000000000000000000000000000000),((335381:ℚ)/5120000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((522143837:ℚ)/625000000),((129051143:ℚ)/125000000),((-250452667:ℚ)/540000000),((-1166431511:ℚ)/5000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2773631994990117427847660500669243001292919857630759973:ℚ)/21093750000000000000000000000000000000000000000000000000),((335381:ℚ)/5120000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((2565037593:ℚ)/2500000000),((14131237247:ℚ)/10000000000),((-86758660729:ℚ)/160000000000),((-6095112779:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4968034631153146588388740763767344056337617769800786611:ℚ)/32850900000000000000000000000000000000000000000000000000),((335381:ℚ)/5120000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source21 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source21 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC10
#check @N11Formalization.C450Source21GroupedC10.bound
#print axioms N11Formalization.C450Source21GroupedC10.valid0
#print axioms N11Formalization.C450Source21GroupedC10.valid1
#print axioms N11Formalization.C450Source21GroupedC10.valid2
#print axioms N11Formalization.C450Source21GroupedC10.valid3
#print axioms N11Formalization.C450Source21GroupedC10.valid4
#print axioms N11Formalization.C450Source21GroupedC10.valid5
#print axioms N11Formalization.C450Source21GroupedC10.valid6
#print axioms N11Formalization.C450Source21GroupedC10.valid7
#print axioms N11Formalization.C450Source21GroupedC10.valid8
#print axioms N11Formalization.C450Source21GroupedC10.valid9
#print axioms N11Formalization.C450Source21GroupedC10.valid10
#print axioms N11Formalization.C450Source21GroupedC10.valid11
#print axioms N11Formalization.C450Source21GroupedC10.valid12
#print axioms N11Formalization.C450Source21GroupedC10.valid13
#print axioms N11Formalization.C450Source21GroupedC10.bound
#print axioms N11Formalization.C450Source21GroupedC10.endpoint_checks
