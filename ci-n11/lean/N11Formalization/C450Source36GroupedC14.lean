import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((1554350563:ℚ)/2500000000),((6430923137:ℚ)/10000000000),((2467230589:ℚ)/101100000000),((1245649437:ℚ)/12400000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((6127331189:ℚ)/10000000000),((-715806477271798907494543017717413011162839672393276359062127:ℚ)/9309966769603125000000000000000000000000000000000000000000000),((-2559529090373941770453467:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((6339189041:ℚ)/10000000000),((1638091753:ℚ)/2500000000),((525724741:ℚ)/25750000000),((4860810959:ℚ)/50550000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((5842902107:ℚ)/10000000000),((-443169835979865138061075978108040621452275409123747261398581:ℚ)/6059566047998046875000000000000000000000000000000000000000000),((-43756365818934141692542483:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((807607453:ℚ)/1250000000),((1303459:ℚ)/1953125),((1358492:ℚ)/81953125),((592392547:ℚ)/6437500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1109192561:ℚ)/2000000000),((-5078843322257359216018754936868342420963145981176777:ℚ)/72992967159992456436157226562500000000000000000000000),((-727703143881420431826787:ℚ)/7220000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((3291210311:ℚ)/5000000000),((3367172791:ℚ)/5000000000),((778481627:ℚ)/52925000000),((2308789689:ℚ)/26225000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2617168033:ℚ)/5000000000),((-34619305627659727240091991064297387175715026733308373169554027:ℚ)/509780945130899072265625000000000000000000000000000000000000000),((-12350620502786571857583203:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((6643161957:ℚ)/10000000000),((6794957953:ℚ)/10000000000),((1375126141:ℚ)/106800000000),((4556838043:ℚ)/52925000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((158504969:ℚ)/312500000),((-282539748345563188580304450963163849211123532844883984635254341:ℚ)/4265259947065350000000000000000000000000000000000000000000000000),((-140781361835560473377987:ℚ)/1280000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((1340775631:ℚ)/2000000000),((6855547831:ℚ)/10000000000),((1193356507:ℚ)/107750000000),((899224369:ℚ)/10680000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4905174167:ℚ)/10000000000),((-23447722459700631699922902089671857603899266245255064018001:ℚ)/362880106951332092285156250000000000000000000000000000000000),((-2089796410251668366623123:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6764569911:ℚ)/10000000000),((691611583:ℚ)/1000000000),((101165251:ℚ)/10870000000),((4435430089:ℚ)/53875000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4732866689:ℚ)/10000000000),((-46993158942227584824451651823706539402716328454775337159579:ℚ)/745578188133696875000000000000000000000000000000000000000000),((-53671009500714110135064803:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((6825237893:ℚ)/10000000000),((348833127:ℚ)/500000000),((41500619:ℚ)/5482500000),((4374762107:ℚ)/54350000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4554626441:ℚ)/10000000000),((-3117496349132508046660228225241197671297230867044461566113:ℚ)/50706517549546032714843750000000000000000000000000000000000),((-152632632922373582982787:ℚ)/1280000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3442941373:ℚ)/5000000000),((1759297133:ℚ)/2500000000),((162108601:ℚ)/27650000000),((2157058627:ℚ)/27412500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4369721297:ℚ)/10000000000),((-99231005383321395434031861894637988859044989867594128756203:ℚ)/1654670267689764404296875000000000000000000000000000000000000),((-14133258491137006779986347:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((1736626273:ℚ)/2500000000),((1774423589:ℚ)/2500000000),((116729233:ℚ)/27887500000),((1063373727:ℚ)/13825000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((835451991:ℚ)/2000000000),((-10825050850112390236794282258881210879030465004177622572919:ℚ)/185059341081854629516601562500000000000000000000000000000000),((-3623061269617165169368547:ℚ)/28880000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((7007105531:ℚ)/10000000000),((3579090271:ℚ)/5000000000),((142729187:ℚ)/56250000000),((4192894469:ℚ)/55775000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((795227761:ℚ)/2000000000),((-1850910305341428655954902584723678663380816288885269995115241:ℚ)/32441283783316612243652343750000000000000000000000000000000000),((-59408229542759815247166523:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7067684639:ℚ)/10000000000),((7279097691:ℚ)/10000000000),((-77293073:ℚ)/112500000000),((4132315361:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1882481797:ℚ)/5000000000),((-241301894390525244502900487445364922392662131197418416087:ℚ)/4449462890625000000000000000000000000000000000000000000000),((-60850791241596823036078003:ℚ)/462080000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((287551243:ℚ)/400000000),((3760439391:ℚ)/5000000000),((-401318173:ℚ)/57200000000),((160448757:ℚ)/2288000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1652314439:ℚ)/5000000000),((-21388778289052723234253267643368862198669918744586395649:ℚ)/438631050000000000000000000000000000000000000000000000000),((-101993422340201277826907:ℚ)/739328000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7430741259:ℚ)/10000000000),((485154297:ℚ)/625000000),((-95462891:ℚ)/7387500000),((3769258741:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((422885771:ℚ)/2000000000),((-165655359931845703184203217842300163198161360935363167:ℚ)/3779755938720703125000000000000000000000000000000000000),((-69576222320381635959054683:ℚ)/462080000000000000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7672416219:ℚ)/10000000000),((824491231:ℚ)/1000000000),((-297473693:ℚ)/12200000000),((3527583781:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-48738007561771894933981694844234770695784208636920763:ℚ)/1418631250000000000000000000000000000000000000000000000),((-20413001:ℚ)/128000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((1631002819:ℚ)/2000000000),((1270936751:ℚ)/1250000000),((-1092810253:ℚ)/16200000000),((608997181:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-548415024034733615893304644055168435597928276805321:ℚ)/2491129687500000000000000000000000000000000000000000000),((-20413001:ℚ)/128000000)⟩
theorem valid15 : Valid source36 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((10078061393:ℚ)/10000000000),((2798762233:ℚ)/2000000000),((-4044286699:ℚ)/32000000000),((1121938607:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1107634129118724753379289643907128397:ℚ)/20480000000000000000000000000000000000),((-20413001:ℚ)/128000000)⟩
theorem valid16 : Valid source36 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC14
#check @N11Formalization.C450Source36GroupedC14.bound
#print axioms N11Formalization.C450Source36GroupedC14.valid0
#print axioms N11Formalization.C450Source36GroupedC14.valid1
#print axioms N11Formalization.C450Source36GroupedC14.valid2
#print axioms N11Formalization.C450Source36GroupedC14.valid3
#print axioms N11Formalization.C450Source36GroupedC14.valid4
#print axioms N11Formalization.C450Source36GroupedC14.valid5
#print axioms N11Formalization.C450Source36GroupedC14.valid6
#print axioms N11Formalization.C450Source36GroupedC14.valid7
#print axioms N11Formalization.C450Source36GroupedC14.valid8
#print axioms N11Formalization.C450Source36GroupedC14.valid9
#print axioms N11Formalization.C450Source36GroupedC14.valid10
#print axioms N11Formalization.C450Source36GroupedC14.valid11
#print axioms N11Formalization.C450Source36GroupedC14.valid12
#print axioms N11Formalization.C450Source36GroupedC14.valid13
#print axioms N11Formalization.C450Source36GroupedC14.valid14
#print axioms N11Formalization.C450Source36GroupedC14.valid15
#print axioms N11Formalization.C450Source36GroupedC14.valid16
#print axioms N11Formalization.C450Source36GroupedC14.bound
#print axioms N11Formalization.C450Source36GroupedC14.endpoint_checks
