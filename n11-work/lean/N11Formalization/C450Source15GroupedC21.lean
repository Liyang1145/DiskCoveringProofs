import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((6002137279:ℚ)/10000000000),((815748019:ℚ)/1250000000),((8082137279:ℚ)/26700000000),((1039748019:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((206370933:ℚ)/312500000),((7631136092692127766997067702171036513:ℚ)/271842636672000000000000000000000000000),((-8527539926509702922997019:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3239384803:ℚ)/5000000000),((6764139271:ℚ)/10000000000),((4279384803:ℚ)/13825000000),((8556139271:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((110020981:ℚ)/200000000),((155665084546206017076944179210999317622429242334740086975477:ℚ)/6208872909724800000000000000000000000000000000000000000000000),((-564558634127553833209776339:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((6717001249:ℚ)/10000000000),((860400021:ℚ)/1250000000),((8797001249:ℚ)/28125000000),((1084400021:ℚ)/2765000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1217098263:ℚ)/2500000000),((36385189126924983318033072283521847555081887307008043:ℚ)/1528806086718750000000000000000000000000000000000000000),((-8967935592012735213507339:ℚ)/46208000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((3418049227:ℚ)/5000000000),((7002250699:ℚ)/10000000000),((4458049227:ℚ)/14300000000),((8794250699:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((904406231:ℚ)/2000000000),((3814941793526713053426381355561887252319838412492092290459:ℚ)/161754785156250000000000000000000000000000000000000000000000),((-578534634929803986086471979:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((1738796019:ℚ)/2500000000),((56970331:ℚ)/80000000),((2258796019:ℚ)/7268750000),((71306331:ℚ)/183040000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((518627591:ℚ)/1250000000),((303161590701213659711391886971552647793332905644760691:ℚ)/12960372286367334400000000000000000000000000000000000000),((-37319509209222641241419:ℚ)/189267968000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/4),((5:ℚ)/16),((27633823:ℚ)/39062500),((7180808167:ℚ)/10000000000),((286070584:ℚ)/916015625),((8972808167:ℚ)/23260000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3741366089:ℚ)/10000000000),((98888567126681924170628849250704598653398981798943153461943:ℚ)/4325086948348337500000000000000000000000000000000000000000000),((-587805351552562708022243731:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((7133792033:ℚ)/10000000000),((452520167:ℚ)/625000000),((3071264011:ℚ)/9850000000),((564520167:ℚ)/1465625000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3520817617:ℚ)/10000000000),((4350520564396262636315644120747072110882420259189394017:ℚ)/190906656483697891235351562500000000000000000000000000000),((-2305054969707118254700731:ℚ)/11552000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((3596661411:ℚ)/5000000000),((1459966989:ℚ)/2000000000),((4636661411:ℚ)/14893750000),((1818366989:ℚ)/4728000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1643081053:ℚ)/5000000000),((28406153884624187953577575199300572226598233446670512138583:ℚ)/1250372032012713600000000000000000000000000000000000000000000),((-23695271659451861039936059:ℚ)/118292480000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3626425559:ℚ)/5000000000),((3679672519:ℚ)/5000000000),((4666425559:ℚ)/15012500000),((4575672519:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((151706167:ℚ)/500000000),((21589222264939974514840741506417612572356400638200386506071:ℚ)/953077439830306982421875000000000000000000000000000000000000),((-148667127954534345237096019:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((7312376979:ℚ)/10000000000),((7478358893:ℚ)/10000000000),((9392376979:ℚ)/30500000000),((9270358893:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((17249611:ℚ)/62500000),((7390486076785893095217321491869658148163392263474419488573:ℚ)/322298805966050000000000000000000000000000000000000000000000),((-596841280447828594417902971:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((7431421627:ℚ)/10000000000),((1543272523:ℚ)/2000000000),((9511421627:ℚ)/31450000000),((1901672523:ℚ)/4880000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((527539757:ℚ)/2500000000),((1685529423030810232173898051931109415524983613815780924883:ℚ)/71842391856800000000000000000000000000000000000000000000000),((-39565976795231549:ℚ)/194560000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((3834742063:ℚ)/5000000000),((795433671:ℚ)/1000000000),((541638007:ℚ)/1800000000),((974633671:ℚ)/2516000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((187477506803901560680733041105968573804627107374775191:ℚ)/8063005323600000000000000000000000000000000000000000000),((-42118657:ℚ)/204800000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((790751353:ℚ)/1000000000),((61608231:ℚ)/62500000),((998751353:ℚ)/4000000000),((72808231:ℚ)/162000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((16449400847093123778415482034794818833671910717:ℚ)/553584375000000000000000000000000000000000000000),((-42118657:ℚ)/204800000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((1226355153:ℚ)/1250000000),((13660812161:ℚ)/10000000000),((1486355153:ℚ)/6900000000),((15452812161:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1519328275817488795248025244784033063683:ℚ)/39002112000000000000000000000000000000000),((-42118657:ℚ)/204800000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC21
#check @N11Formalization.C450Source15GroupedC21.bound
#print axioms N11Formalization.C450Source15GroupedC21.valid0
#print axioms N11Formalization.C450Source15GroupedC21.valid1
#print axioms N11Formalization.C450Source15GroupedC21.valid2
#print axioms N11Formalization.C450Source15GroupedC21.valid3
#print axioms N11Formalization.C450Source15GroupedC21.valid4
#print axioms N11Formalization.C450Source15GroupedC21.valid5
#print axioms N11Formalization.C450Source15GroupedC21.valid6
#print axioms N11Formalization.C450Source15GroupedC21.valid7
#print axioms N11Formalization.C450Source15GroupedC21.valid8
#print axioms N11Formalization.C450Source15GroupedC21.valid9
#print axioms N11Formalization.C450Source15GroupedC21.valid10
#print axioms N11Formalization.C450Source15GroupedC21.valid11
#print axioms N11Formalization.C450Source15GroupedC21.valid12
#print axioms N11Formalization.C450Source15GroupedC21.valid13
#print axioms N11Formalization.C450Source15GroupedC21.bound
#print axioms N11Formalization.C450Source15GroupedC21.endpoint_checks
