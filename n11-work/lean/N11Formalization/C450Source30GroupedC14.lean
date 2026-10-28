import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((779655377:ℚ)/1250000000),((3276679629:ℚ)/5000000000),((-870038887:ℚ)/49600000000),((380344623:ℚ)/6200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3040894821:ℚ)/5000000000),((45879173823250593412715866219048169:ℚ)/984064000000000000000000000000000000),((-805764794794748557394869:ℚ)/5776000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((1295756981:ℚ)/2000000000),((6673978943:ℚ)/10000000000),((-2101936829:ℚ)/103000000000),((560243019:ℚ)/10300000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5501010543:ℚ)/10000000000),((1270938597441480803172658788815722957516975887210400759:ℚ)/26677905273437500000000000000000000000000000000000000000),((-2254453037941737406191021:ℚ)/14786560000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((1649860839:ℚ)/2500000000),((3397265291:ℚ)/5000000000),((-1231795873:ℚ)/52450000000),((670139161:ℚ)/13112500000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((5189351107:ℚ)/10000000000),((44264431761120103046516563004476895003521055542635432707:ℚ)/901813007031250000000000000000000000000000000000000000000),((-30525151633848568871863:ℚ)/192000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6720032317:ℚ)/10000000000),((138300357:ℚ)/200000000),((-56501071:ℚ)/2136000000),((853322561:ℚ)/17800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4859861269:ℚ)/10000000000),((341586122138225137893129630287601391679000980555901:ℚ)/6767702400000000000000000000000000000000000000000000),((-61189993402544605904552829:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((6840555543:ℚ)/10000000000),((348761921:ℚ)/500000000),((-150285763:ℚ)/5435000000),((2439444457:ℚ)/54350000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1127147713:ℚ)/2500000000),((3191793483996120786984159351169760480519427693794657:ℚ)/62713159326171875000000000000000000000000000000000000),((-190854263834914375769712367:ℚ)/1108992000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((1380158721:ℚ)/2000000000),((7035444157:ℚ)/10000000000),((-3186332471:ℚ)/109650000000),((475841279:ℚ)/10965000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4323128531:ℚ)/10000000000),((64569658262523902389546002763684670710110667872183191:ℚ)/1252408593750000000000000000000000000000000000000000000),((-7780271939845246192603903:ℚ)/44359680000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6961016521:ℚ)/10000000000),((178895317:ℚ)/250000000),((-88685951:ℚ)/2765000000),((2318983479:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((25812133:ℚ)/62500000),((1002291921254640221879971558973383318309810057016923:ℚ)/18874149218750000000000000000000000000000000000000000),((-66055429084031932316044901:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((3540709247:ℚ)/5000000000),((3638063187:ℚ)/5000000000),((-1954189561:ℚ)/56250000000),((122143417:ℚ)/3125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3715503601:ℚ)/10000000000),((248808183774879470575138929507987324376017367974555977:ℚ)/4577636718750000000000000000000000000000000000000000000),((-17125516646550394777982549:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((7201764483:ℚ)/10000000000),((3758300059:ℚ)/5000000000),((-2314900177:ℚ)/57200000000),((2078235517:ℚ)/57200000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((812892449:ℚ)/2500000000),((16751617182081715403558847682454061197373604808620665707:ℚ)/292420700000000000000000000000000000000000000000000000000),((-212874140446690571765648887:ℚ)/1108992000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((116285931:ℚ)/156250000),((7756885339:ℚ)/10000000000),((-5350656017:ℚ)/118200000000),((28714069:ℚ)/923437500),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2040696711:ℚ)/10000000000),((68269909480511808178770590597456029687626178763913450523:ℚ)/1146805950000000000000000000000000000000000000000000000000),((-55589505905200951037263:ℚ)/270750000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((3841321101:ℚ)/5000000000),((411847899:ℚ)/500000000),((-339543697:ℚ)/6100000000),((798678899:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((22999286901225378309950628325645600162473784750581947:ℚ)/354657812500000000000000000000000000000000000000000000),((-5481981:ℚ)/25600000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((1632563843:ℚ)/2000000000),((253809331:ℚ)/250000000),((-313427993:ℚ)/3240000000),((74478719:ℚ)/4320000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((42534031659619158720345367190572127012985361852801:ℚ)/492075000000000000000000000000000000000000000000000),((-5481981:ℚ)/25600000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((503903411:ℚ)/500000000),((1746297491:ℚ)/1250000000),((-2998892473:ℚ)/20000000000),((-13301137:ℚ)/1840000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((127488345478954902913132802543740756409:ℚ)/1058000000000000000000000000000000000000),((-5481981:ℚ)/25600000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC14
#check @N11Formalization.C450Source30GroupedC14.bound
#print axioms N11Formalization.C450Source30GroupedC14.valid0
#print axioms N11Formalization.C450Source30GroupedC14.valid1
#print axioms N11Formalization.C450Source30GroupedC14.valid2
#print axioms N11Formalization.C450Source30GroupedC14.valid3
#print axioms N11Formalization.C450Source30GroupedC14.valid4
#print axioms N11Formalization.C450Source30GroupedC14.valid5
#print axioms N11Formalization.C450Source30GroupedC14.valid6
#print axioms N11Formalization.C450Source30GroupedC14.valid7
#print axioms N11Formalization.C450Source30GroupedC14.valid8
#print axioms N11Formalization.C450Source30GroupedC14.valid9
#print axioms N11Formalization.C450Source30GroupedC14.valid10
#print axioms N11Formalization.C450Source30GroupedC14.valid11
#print axioms N11Formalization.C450Source30GroupedC14.valid12
#print axioms N11Formalization.C450Source30GroupedC14.bound
#print axioms N11Formalization.C450Source30GroupedC14.endpoint_checks
