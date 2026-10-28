import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((6311177807:ℚ)/10000000000),((1659268151:ℚ)/2500000000),((-419268151:ℚ)/6200000000),((1546466579:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5909385647:ℚ)/10000000000),((57634558461249158877113614166427127:ℚ)/1489550000000000000000000000000000000),((-2852749469943298917128899:ℚ)/40960000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6553525657:ℚ)/10000000000),((1689511069:ℚ)/2500000000),((-449511069:ℚ)/6437500000),((819423029:ℚ)/103000000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5309903207:ℚ)/10000000000),((25868770677194007231589656021946765290701855427837:ℚ)/651316046714782714843750000000000000000000000000000),((-3418238827028621313421299:ℚ)/40960000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1668641003:ℚ)/2500000000),((6818499379:ℚ)/10000000000),((-1858499379:ℚ)/26225000000),((114076991:ℚ)/26225000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((997286951:ℚ)/2000000000),((453223165723691045310687413086593069263072405065446507:ℚ)/11272662587890625000000000000000000000000000000000000000),((-83560049670042942493208899:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6735034149:ℚ)/10000000000),((1719733687:ℚ)/2500000000),((-479733687:ℚ)/6615625000),((274897553:ℚ)/105850000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2408714903:ℚ)/5000000000),((1866086037791938968088268166518051949639987111103311:ℚ)/45241048874855041503906250000000000000000000000000000),((-1388661882449408073155525411:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((1698858091:ℚ)/2500000000),((277574037:ℚ)/400000000),((-79174037:ℚ)/1068000000),((23425727:ℚ)/26700000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4642986719:ℚ)/10000000000),((96542354472863807862528908155177821766340744783663:ℚ)/2284099560000000000000000000000000000000000000000000),((-90029422784422335662772291:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((1713953019:ℚ)/2500000000),((6999748431:ℚ)/10000000000),((-2039748431:ℚ)/26937500000),((-21859057:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2231149807:ℚ)/5000000000),((528552465778791713401669964142471190262903567400601183:ℚ)/12216642913818359375000000000000000000000000000000000000),((-93277055197602190391459171:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((3458086893:ℚ)/5000000000),((3530063883:ℚ)/5000000000),((-1050063883:ℚ)/13587500000),((-7897687:ℚ)/3225000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((534321387:ℚ)/1250000000),((13005709718640654521343330390464967684552307482264073:ℚ)/293967934341430664062500000000000000000000000000000000),((-386137129024609372289878739:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((3488258989:ℚ)/5000000000),((1424097883:ℚ)/2000000000),((-432097883:ℚ)/5482500000),((-224776967:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((163152929:ℚ)/400000000),((108261844997584849516645466491625772499673351719273:ℚ)/2395231435546875000000000000000000000000000000000000),((-399204483021168454476616531:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7036845117:ℚ)/10000000000),((3620580753:ℚ)/5000000000),((-1140580753:ℚ)/13825000000),((-630535351:ℚ)/112500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3873834537:ℚ)/10000000000),((11241809739461217952001275708623825165193194556581863:ℚ)/235926865234375000000000000000000000000000000000000000),((-1649241388768251027867139379:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((357872501:ℚ)/500000000),((3680884123:ℚ)/5000000000),((-1200884123:ℚ)/14062500000),((-3816731:ℚ)/440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3429411929:ℚ)/10000000000),((85923939053648134040058293460487314137948792098182931:ℚ)/1738071441650390625000000000000000000000000000000000000),((-4386378536168355969134211:ℚ)/36966400000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7277991907:ℚ)/10000000000),((3801399329:ℚ)/5000000000),((-1321399329:ℚ)/14300000000),((-1353975721:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((584274653:ℚ)/2000000000),((24693530192273340243426246586236835281940633942099593:ℚ)/456907343750000000000000000000000000000000000000000000),((-1860480486421578435225453939:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((3759449571:ℚ)/5000000000),((1960901131:ℚ)/2500000000),((-240300377:ℚ)/2462500000),((-1038348713:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1462203729:ℚ)/10000000000),((1601065128834530735279522234530614696937057688675483:ℚ)/27998192138671875000000000000000000000000000000000000),((-518550677358048449056481651:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((121243591:ℚ)/156250000),((4162311833:ℚ)/5000000000),((-1682311833:ℚ)/15250000000),((-43730773:ℚ)/2025000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((36255844415043962039657438668801190157504895165255329:ℚ)/554152832031250000000000000000000000000000000000000000),((-148667409:ℚ)/1024000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8240399613:ℚ)/10000000000),((2560725701:ℚ)/2500000000),((-1320725701:ℚ)/8100000000),((-4241198839:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6204023961834604094116346520012926472443133246526999:ℚ)/62278242187500000000000000000000000000000000000000000),((-148667409:ℚ)/1024000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10158045637:ℚ)/10000000000),((7032117579:ℚ)/5000000000),((-4552117579:ℚ)/20000000000),((-9994136911:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((149827266578163848663185481356878737:ℚ)/1000000000000000000000000000000000000),((-148667409:ℚ)/1024000000)⟩
theorem valid14 : Valid source33 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source33 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source33 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC13
#check @N11Formalization.C450Source33GroupedC13.bound
#print axioms N11Formalization.C450Source33GroupedC13.valid0
#print axioms N11Formalization.C450Source33GroupedC13.valid1
#print axioms N11Formalization.C450Source33GroupedC13.valid2
#print axioms N11Formalization.C450Source33GroupedC13.valid3
#print axioms N11Formalization.C450Source33GroupedC13.valid4
#print axioms N11Formalization.C450Source33GroupedC13.valid5
#print axioms N11Formalization.C450Source33GroupedC13.valid6
#print axioms N11Formalization.C450Source33GroupedC13.valid7
#print axioms N11Formalization.C450Source33GroupedC13.valid8
#print axioms N11Formalization.C450Source33GroupedC13.valid9
#print axioms N11Formalization.C450Source33GroupedC13.valid10
#print axioms N11Formalization.C450Source33GroupedC13.valid11
#print axioms N11Formalization.C450Source33GroupedC13.valid12
#print axioms N11Formalization.C450Source33GroupedC13.valid13
#print axioms N11Formalization.C450Source33GroupedC13.valid14
#print axioms N11Formalization.C450Source33GroupedC13.bound
#print axioms N11Formalization.C450Source33GroupedC13.endpoint_checks
